import { regularFileCancellation } from "../filesystem/OwnedRegularFile.js";
import { createHash, randomUUID } from "node:crypto";
import { createWriteStream } from "node:fs";
import {
  access,
  chmod,
  mkdir,
  mkdtemp,
  opendir,
  open,
  rm,
  stat,
} from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Transform, type TransformCallback } from "node:stream";
import { pipeline } from "node:stream/promises";
import type { FileHandle } from "node:fs/promises";

import type {
  ExecutionOptions,
  ProviderAvailability,
} from "../application/AnalysisProvider.js";
import { providerConfigurationRefusal } from "../domain/providerConfigurationRefusal.js";
import {
  createAnalysisExecution,
  type AnalysisExecution,
} from "../application/AnalysisProvider.js";
import {
  androidLocaleQualifierSchema,
  AGGREGATE_STRINGS_XML_MAX_BYTES,
  MAX_AGGREGATE_STRINGS,
  MAX_STRINGS,
  type ApktoolRequest,
  type StringTable,
} from "../domain/apktool/apktoolResourceAnalysis.js";
import {
  AnalysisCapabilityUnavailableError,
  AnalysisCancelledError,
  AnalysisInputError,
  AnalysisProtocolError,
  AnalysisResourceConstraintError,
  AnalysisTimeoutError,
  AnalysisUnsupportedTargetError,
} from "../domain/analysisErrorCore.js";
import type { AnalysisError } from "../domain/analysisErrorBase.js";
import { analysisErrorWithCleanupFailure } from "../domain/analysisErrorCleanup.js";
import { err, ok, type Result } from "../domain/result.js";
import { ProviderCleanupError } from "../domain/providerCleanupError.js";
import {
  openRegularFile,
  sameRegularFileState,
} from "../filesystem/RegularFile.js";
import {
  OwnedCommandFailure,
  runOwnedCommand,
} from "../process/OwnedCommand.js";
import type { ProviderProcessSupervisor } from "../process/ProviderProcess.js";
import { snapshotEnvironment } from "../process/snapshotEnvironment.js";
import { WindowsBatchCommandError } from "../process/WindowsBatchCommand.js";
import {
  APKTOOL_COMMAND_ENV,
  ApktoolConfigurationFailure,
  type ApktoolProbeCleanup,
  apktoolConfigurationAvailability,
  apktoolInvocation,
  inspectApktoolClient,
  resolveApktoolCommand,
  type ApktoolCommandSelection,
  type ApktoolClientIdentity,
} from "./ApktoolConfiguration.js";
import {
  parseApktoolYml,
  parseDecodedStrings,
  parseManifestPackage,
} from "./ApktoolDecodeOutput.js";

/** Stable identity for the Apktool resource-decoding provider. */
export const APKTOOL_PROVIDER_IDENTITY = {
  id: "apktool",
  name: "Apktool",
  version: null,
} as const;

const DECODE_TIMEOUT_MS = 600_000;
const DECODE_MAX_OUTPUT_BYTES = 4 * 1024 * 1024;
const MANIFEST_MAX_BYTES = 512 * 1024;
const STRINGS_XML_MAX_BYTES = 8 * 1024 * 1024;
const MAX_DECODED_ENTRIES_VISITED = 100_000;
const STDERR_EXCERPT_BYTES = 512;

const throwIfCancelled = (
  operation: string,
  signal: AbortSignal | undefined,
): void => {
  if (signal?.aborted === true) throw new AnalysisCancelledError(operation);
};

/** Read at most the byte budget plus one byte, before decoding UTF-8. */
const readBoundedText = async (
  path: string,
  budget: number,
  operation: string,
  signal: AbortSignal | undefined,
): Promise<{ text: string | null; truncated: boolean; bytesRead: number }> => {
  const file = await open(path, "r").catch((cause: unknown) => {
    if ((cause as NodeJS.ErrnoException).code === "ENOENT") return null;
    throw cause;
  });
  if (file === null) return { text: null, truncated: false, bytesRead: 0 };
  let length = 0;
  try {
    throwIfCancelled(operation, signal);
    const bytes = Buffer.alloc(budget + 1);
    while (length < bytes.length) {
      throwIfCancelled(operation, signal);
      const result = await file.read(
        bytes,
        length,
        bytes.length - length,
        null,
      );
      if (result.bytesRead === 0) break;
      length += result.bytesRead;
    }
    throwIfCancelled(operation, signal);
    const truncated = length > budget;
    // A prefix may end within a UTF-8 character; omit those trailing bytes.
    try {
      const decoder = new TextDecoder("utf-8", { fatal: true });
      return {
        text: decoder.decode(bytes.subarray(0, Math.min(length, budget)), {
          stream: truncated,
        }),
        truncated,
        bytesRead: length,
      };
    } catch (cause: unknown) {
      const error = new AnalysisProtocolError(
        `apktool produced invalid UTF-8 in ${path}`,
        { cause },
      );
      (error as unknown as { bytesRead: number }).bytesRead = length;
      throw error;
    }
  } finally {
    await file.close();
  }
};

const localeQualifier = (locale: string): string =>
  locale.replace(/^([a-z]{2,3})-([A-Z]{2}|[0-9]{3})$/u, "$1-r$2");

interface DecodeLimits {
  readonly timeoutMs: number;
  readonly maxOutputBytes: number;
}

/** A probe whose launched processes could not be confirmed stopped. */
const probeCleanupFailure = (
  operation: string,
  failure: ApktoolConfigurationFailure,
  cleanup: ApktoolProbeCleanup,
): ProviderCleanupError =>
  new ProviderCleanupError(
    APKTOOL_PROVIDER_IDENTITY.id,
    cleanup.resources,
    { reason: cleanup.reason, probe_failure: failure.message },
    { operation, cause: failure },
  );

const runApktool = async (
  operation: string,
  selection: ApktoolCommandSelection,
  arguments_: readonly string[],
  limits: DecodeLimits,
  signal: AbortSignal | undefined,
  environment: Readonly<Record<string, string | undefined>>,
  onCleanupOwner: (owner: ProviderProcessSupervisor) => void,
): Promise<Result<{ stdout: string; stderr: string }, AnalysisError>> => {
  if (signal?.aborted === true)
    return err(new AnalysisCancelledError(operation));
  let invocation: ReturnType<typeof apktoolInvocation>;
  try {
    invocation = apktoolInvocation(selection, arguments_, environment);
  } catch (cause) {
    if (!(cause instanceof WindowsBatchCommandError)) throw cause;
    const reason = `The apktool batch launcher cannot receive REA's decode paths through cmd.exe: ${cause.message}`;
    return err(
      new AnalysisCapabilityUnavailableError(
        APKTOOL_PROVIDER_IDENTITY.id,
        operation,
        reason,
        { cause, userMessage: reason },
      ),
    );
  }
  try {
    const output = await runOwnedCommand(
      {
        command: invocation.command,
        arguments: invocation.arguments,
        windowsVerbatimArguments: invocation.windowsVerbatimArguments,
        // Apktool launchers are commonly interpreter scripts, so ownership is
        // proved by the run token rather than the launcher's argv prefix.
        expectedCommand: null,
        runId: randomUUID(),
        hostEnvironment: environment,
      },
      {
        timeoutMs: limits.timeoutMs,
        diagnosticBytes: limits.maxOutputBytes,
      },
      signal === undefined ? {} : { signal },
    );
    return ok({ stdout: output.stdout.text, stderr: output.stderr.text });
  } catch (cause) {
    if (!(cause instanceof OwnedCommandFailure))
      return err(
        new AnalysisProtocolError(`apktool failed for ${operation}`, { cause }),
      );
    if (cause.cleanupOwner !== undefined) onCleanupOwner(cause.cleanupOwner);
    const output = cause.snapshot;
    const capturedOutput =
      output === null
        ? undefined
        : {
            stdout: output.stdout.text,
            stderr: output.stderr.text,
            truncated: output.diagnosticTruncated === true,
            stdout_bytes: output.stdout.bytes,
            stderr_bytes: output.stderr.bytes,
            exit_code: output.exitCode ?? null,
            signal: output.signal ?? null,
          };
    const cleanup =
      cause.cleanupFailure === null
        ? undefined
        : {
            reason: cause.cleanupFailure,
            resources: cause.resources,
          };
    if (cause.reason === "cancelled")
      return err(
        new AnalysisCancelledError(operation, {
          cause,
          ...(cleanup === undefined ? {} : { cleanup }),
          ...(capturedOutput === undefined ? {} : { capturedOutput }),
        }),
      );
    if (cause.reason === "timeout")
      return err(
        new AnalysisTimeoutError(operation, limits.timeoutMs, {
          cause,
          ...(cleanup === undefined ? {} : { cleanup }),
          ...(capturedOutput === undefined ? {} : { capturedOutput }),
        }),
      );
    if (cause.reason === "output-limit")
      return err(
        new AnalysisResourceConstraintError(
          operation,
          "memory",
          `apktool output exceeded the ${String(limits.maxOutputBytes)}-byte capture budget`,
          { max_output_bytes: limits.maxOutputBytes },
          {
            cause,
            ...(cleanup === undefined ? {} : { cleanup }),
            ...(capturedOutput === undefined ? {} : { capturedOutput }),
          },
        ),
      );
    return err(
      new AnalysisUnsupportedTargetError(
        operation,
        selection.command,
        output?.stderr.text.trim().slice(0, STDERR_EXCERPT_BYTES) ||
          `apktool exited with code ${String(output?.exitCode ?? "unknown")} for ${operation}`,
        {
          cause,
          ...(cleanup === undefined ? {} : { cleanup }),
          ...(capturedOutput === undefined ? {} : { capturedOutput }),
        },
      ),
    );
  }
};

/** Count files while bounding streamed directory-entry traversal. */
const countDecodedFiles = async (
  root: string,
  signal: AbortSignal | undefined,
  operation: string,
): Promise<{
  count: number;
  capped: boolean;
  locales: readonly string[];
}> => {
  let count = 0;
  let capped = false;
  let visited = 0;
  const directories = [root];
  const locales: string[] = [];
  while (directories.length > 0 && !capped) {
    throwIfCancelled(operation, signal);
    const directory = directories.pop()!;
    for await (const entry of await opendir(directory)) {
      throwIfCancelled(operation, signal);
      if (visited >= MAX_DECODED_ENTRIES_VISITED) {
        capped = true;
        break;
      }
      visited += 1;
      const path = join(directory, entry.name);
      if (entry.isDirectory()) {
        directories.push(path);
        if (directory === join(root, "res")) {
          const match = /^values-(.+)$/u.exec(entry.name);
          if (
            match !== null &&
            androidLocaleQualifierSchema.safeParse(match[1]).success &&
            (await access(join(path, "strings.xml")).then(
              () => true,
              () => false,
            ))
          )
            locales.push(match[1]!);
        }
      } else if (entry.isFile()) count += 1;
    }
  }
  return { count, capped, locales: locales.sort() };
};

export interface ApktoolProviderOptions {
  readonly environment?: Readonly<Record<string, string | undefined>>;
  readonly removeWorkspace?: (path: string) => Promise<void>;
}

/**
 * Apktool resource decoding over a caller-selected launcher.
 *
 * Decoding happens in a provider-owned temporary workspace that is removed
 * once the requested facts are projected; smali production is skipped
 * (`--no-src`) because Java-source recovery belongs to the JADX family.
 */
export class ApktoolProvider {
  private readonly selectedEnvironment:
    | Readonly<Record<string, string | undefined>>
    | undefined;

  private readonly workspaces = new Set<string>();
  private readonly removeWorkspace: (path: string) => Promise<void>;
  readonly #pendingCommandOwners = new Map<ProviderProcessSupervisor, string>();
  /** A version probe whose cleanup is unresolved is retried on close. */
  readonly #retainProbeOwner = (owner: ProviderProcessSupervisor): void => {
    this.#pendingCommandOwners.set(owner, "apktool version probe");
  };
  readonly #shutdown = new AbortController();
  readonly #active = new Set<Promise<void>>();
  #closing = false;
  #closePromise: Promise<void> | undefined;

  constructor(options: ApktoolProviderOptions = {}) {
    this.selectedEnvironment =
      options.environment === undefined
        ? undefined
        : snapshotEnvironment(options.environment);
    this.removeWorkspace =
      options.removeWorkspace ??
      ((path) => rm(path, { recursive: true, force: true }));
  }

  private operationEnvironment(): Readonly<NodeJS.ProcessEnv> {
    const ambient = snapshotEnvironment(process.env);
    if (this.selectedEnvironment === undefined) return ambient;
    // Child inheritance is sampled per operation. An explicit map keeps its
    // launcher choice authoritative, including an omitted command selecting PATH.
    return snapshotEnvironment({
      ...ambient,
      ...this.selectedEnvironment,
      [APKTOOL_COMMAND_ENV]: this.selectedEnvironment[APKTOOL_COMMAND_ENV],
    });
  }

  /** Probe the selected apktool launcher; decodes nothing. */
  inspectAvailability(signal?: AbortSignal): Promise<ProviderAvailability> {
    if (this.#closing)
      return Promise.reject(
        new AnalysisCancelledError("inspect_apktool_client"),
      );
    const operationSignal =
      signal === undefined
        ? this.#shutdown.signal
        : AbortSignal.any([signal, this.#shutdown.signal]);
    return this.#track(this.#inspectAvailability(operationSignal));
  }

  async #inspectAvailability(
    signal: AbortSignal,
  ): Promise<ProviderAvailability> {
    const environment = this.operationEnvironment();
    try {
      const selection = await resolveApktoolCommand(
        environment,
        process.platform,
        signal,
      );
      await inspectApktoolClient(
        selection,
        signal,
        environment,
        process.platform,
        this.#retainProbeOwner,
      );
      throwIfCancelled("inspect_apktool_client", signal);
      return {
        status: "available",
        code: null,
        reason: null,
        diagnostics: {
          selected_command: selection.command,
          command_source: selection.commandSource,
        },
      };
    } catch (cause) {
      if (cause instanceof ApktoolConfigurationFailure) {
        if (cause.cleanup !== undefined)
          throw probeCleanupFailure(
            "inspect_apktool_client",
            cause,
            cause.cleanup,
          );
        return apktoolConfigurationAvailability(cause);
      }
      throw cause;
    }
  }

  /** Retain failed cleanup ownership and retry it on close. */
  async close(): Promise<void> {
    this.#closing = true;
    this.#shutdown.abort();
    this.#closePromise ??= this.#drainAndClean().catch((cause: unknown) => {
      this.#closePromise = undefined;
      throw cause;
    });
    return this.#closePromise;
  }

  execute(
    request: ApktoolRequest,
    options?: ExecutionOptions,
  ): Promise<Result<AnalysisExecution, AnalysisError>> {
    if (this.#closing)
      return Promise.resolve(
        err(new AnalysisCancelledError(request.operation)),
      );
    const signal =
      options?.signal === undefined
        ? this.#shutdown.signal
        : AbortSignal.any([options.signal, this.#shutdown.signal]);
    return this.#track(this.#execute(request, signal));
  }

  async #execute(
    request: ApktoolRequest,
    signal: AbortSignal,
  ): Promise<Result<AnalysisExecution, AnalysisError>> {
    if (signal?.aborted === true)
      return err(new AnalysisCancelledError(request.operation));
    const environment = this.operationEnvironment();
    let selection: ApktoolCommandSelection;
    let identity: ApktoolClientIdentity;
    try {
      selection = await resolveApktoolCommand(
        environment,
        process.platform,
        signal,
      );
      identity = await inspectApktoolClient(
        selection,
        signal,
        environment,
        process.platform,
        this.#retainProbeOwner,
      );
    } catch (cause) {
      if (
        cause instanceof AnalysisCancelledError ||
        cause instanceof AnalysisTimeoutError
      )
        return err(cause);
      if (cause instanceof ApktoolConfigurationFailure) {
        if (cause.cleanup !== undefined)
          return err(
            probeCleanupFailure(request.operation, cause, cause.cleanup),
          );
        return err(
          providerConfigurationRefusal(
            APKTOOL_PROVIDER_IDENTITY.id,
            request.operation,
            cause,
          ),
        );
      }
      return err(
        new AnalysisProtocolError(
          `apktool version probe failed for ${request.operation}`,
          { cause },
        ),
      );
    }
    if (signal.aborted)
      return err(new AnalysisCancelledError(request.operation));
    const client = {
      command: selection.command,
      command_source: selection.commandSource,
      apktool_version: identity.version,
    };
    const provider = {
      ...APKTOOL_PROVIDER_IDENTITY,
      version: identity.version,
    };
    if (request.operation === "inspect_apktool_client")
      return ok(createAnalysisExecution({ client }, provider));
    return this.decodeResources(
      request.operation,
      selection,
      environment,
      client,
      provider,
      request.input,
      signal,
    );
  }

  #track<T>(operation: Promise<T>): Promise<T> {
    const settled = operation.then(
      () => undefined,
      () => undefined,
    );
    this.#active.add(settled);
    void settled.then(() => this.#active.delete(settled));
    return operation;
  }

  async #drainAndClean(): Promise<void> {
    await Promise.all(this.#active);
    const failures: unknown[] = [];
    const retained: string[] = [];
    for (const [owner, root] of this.#pendingCommandOwners) {
      try {
        const stopped = await owner.stop();
        if (stopped.status === "incomplete") throw new Error(stopped.reason);
        this.#pendingCommandOwners.delete(owner);
      } catch (cause) {
        retained.push(root);
        failures.push(
          new Error(
            `apktool process cleanup remains incomplete for ${root}: ${cause instanceof Error ? cause.message : String(cause)}`,
            { cause },
          ),
        );
      }
    }
    // Ownership stays retained for a later close; report it as typed cleanup.
    if (failures.length > 0)
      throw new ProviderCleanupError(
        APKTOOL_PROVIDER_IDENTITY.id,
        retained,
        {
          reason: failures
            .map((failure) =>
              failure instanceof Error ? failure.message : String(failure),
            )
            .join("; "),
        },
        {
          operation: "close",
          cause: new AggregateError(failures, "Apktool process cleanup failed"),
        },
      );
    for (const path of this.workspaces) {
      try {
        await this.removeWorkspace(path);
        this.workspaces.delete(path);
      } catch (cause) {
        failures.push(cause);
      }
    }
    if (failures.length > 0)
      throw new AggregateError(failures, "Apktool workspace cleanup failed");
  }

  private async decodeResources(
    operation: "decode_android_resources",
    selection: ApktoolCommandSelection,
    environment: Readonly<NodeJS.ProcessEnv>,
    client: {
      command: string;
      command_source: string;
      apktool_version: string | null;
    },
    provider: { id: string; name: string; version: string | null },
    input: {
      readonly path: string;
      readonly include_strings: boolean;
      readonly locale?: string | undefined;
      readonly locales?: readonly string[] | undefined;
    },
    signal: AbortSignal | undefined,
  ): Promise<Result<AnalysisExecution, AnalysisError>> {
    const root = await mkdtemp(join(tmpdir(), "rea-apktool-"));
    this.workspaces.add(root);
    const workspace = join(root, "decoded");
    const snapshot = join(root, "input.apk");
    const framework = join(root, "framework");
    let cleanupFailure: string | null = null;
    // The workspace is removed before the result is returned, so an
    // unremovable workspace is reported instead of silently abandoned.
    const removeWorkspace = async (): Promise<void> => {
      if ([...this.#pendingCommandOwners.values()].includes(root)) {
        cleanupFailure = `The decode workspace is retained until its apktool process stops: ${root}`;
        return;
      }
      try {
        await this.removeWorkspace(root);
        this.workspaces.delete(root);
      } catch {
        cleanupFailure = `The decode workspace could not be removed: ${root}`;
      }
    };
    const failureWithCleanup = (failure: AnalysisError): AnalysisError =>
      cleanupFailure === null
        ? failure
        : analysisErrorWithCleanupFailure(
            failure,
            new ProviderCleanupError(
              APKTOOL_PROVIDER_IDENTITY.id,
              [root],
              { reason: cleanupFailure },
              { operation },
            ),
            operation,
          );
    let source: FileHandle | undefined;
    let sourceAdmissionFailed = false;
    try {
      throwIfCancelled(operation, signal);
      sourceAdmissionFailed = true;
      source = await openRegularFile(input.path, {
        symlinks: "follow",
        ...(signal === undefined ? {} : { signal }),
      });
      const sourceInfo = await source.stat();
      sourceAdmissionFailed = false;
      const sourceSize = sourceInfo.size;
      let copiedBytes = 0;
      const sourceHash = createHash("sha256");
      const boundedSource = new Transform({
        transform(
          chunk: Buffer,
          _encoding: BufferEncoding,
          callback: TransformCallback,
        ) {
          copiedBytes += chunk.length;
          if (copiedBytes > sourceSize) {
            callback(
              new AnalysisInputError(operation, {
                cause: new Error(
                  `The selected APK changed while being copied: ${input.path}`,
                ),
              }),
            );
            return;
          }
          sourceHash.update(chunk);
          callback(null, chunk);
        },
      });
      await pipeline(
        source.createReadStream({
          start: 0,
          end: sourceSize,
          autoClose: false,
          ...(signal === undefined ? {} : { signal }),
        }),
        boundedSource,
        createWriteStream(snapshot, { flags: "wx", mode: 0o600 }),
        signal === undefined ? {} : { signal },
      );
      const finalSourceInfo = await source.stat();
      if (
        copiedBytes !== sourceSize ||
        !sameRegularFileState(sourceInfo, finalSourceInfo)
      )
        throw new AnalysisInputError(operation, {
          cause: new Error(
            `The selected APK changed while being copied: ${input.path}`,
          ),
        });
      const sha256 = sourceHash.digest("hex");
      await source.close();
      source = undefined;
      await chmod(snapshot, 0o400);
      throwIfCancelled(operation, signal);
      const snapshotInfo = await stat(snapshot);
      await mkdir(workspace);
      await mkdir(framework);
      const decoded = await runApktool(
        operation,
        selection,
        [
          "d",
          "--no-src",
          "-f",
          "-o",
          workspace,
          "--frame-path",
          framework,
          snapshot,
        ],
        {
          timeoutMs: DECODE_TIMEOUT_MS,
          maxOutputBytes: DECODE_MAX_OUTPUT_BYTES,
        },
        signal,
        environment,
        (owner) => this.#pendingCommandOwners.set(owner, root),
      );
      if (!decoded.ok) {
        await removeWorkspace();
        return err(failureWithCleanup(decoded.error));
      }
      throwIfCancelled(operation, signal);
      const yml = await readBoundedText(
        join(workspace, "apktool.yml"),
        MANIFEST_MAX_BYTES,
        operation,
        signal,
      );
      if (yml.text === null || yml.truncated) {
        throw new AnalysisProtocolError(
          `apktool produced missing or oversized apktool.yml: ${input.path}`,
        );
      }
      const metadata = parseApktoolYml(yml.text);
      const manifestRead = await readBoundedText(
        join(workspace, "AndroidManifest.xml"),
        MANIFEST_MAX_BYTES,
        operation,
        signal,
      );
      const manifest = manifestRead.text;
      const packageName =
        manifest === null || manifestRead.truncated
          ? null
          : parseManifestPackage(manifest);
      const requestedLocales: Array<{
        readonly locale: string | null;
        readonly isPrimary: boolean;
      }> = [];

      if (input.include_strings) {
        requestedLocales.push({
          locale: input.locale ?? null,
          isPrimary: true,
        });

        if (input.locales !== undefined) {
          for (const loc of input.locales) {
            if (!requestedLocales.some((r) => r.locale === loc)) {
              requestedLocales.push({ locale: loc, isPrimary: false });
            }
          }
        }
      }

      let aggregateXmlBytes = 0;
      let aggregateStringsCount = 0;
      let aggregateCapped = false;
      const stringTables: StringTable[] = [];
      const tableLimitations: string[] = [];
      const projectedByDir = new Map<string, StringTable>();

      for (const item of requestedLocales) {
        throwIfCancelled(operation, signal);
        const loc = item.locale;
        const dirName =
          loc === null ? "values" : `values-${localeQualifier(loc)}`;
        const filePath = join(workspace, "res", dirName, "strings.xml");
        const tableLabel =
          loc === null
            ? "default res/values/strings.xml"
            : `res/values-${loc}/strings.xml`;

        if (projectedByDir.has(dirName)) {
          const cached = projectedByDir.get(dirName)!;
          stringTables.push({
            ...cached,
            locale: loc,
          });
          continue;
        }

        const remainingXmlBudget = Math.max(
          0,
          AGGREGATE_STRINGS_XML_MAX_BYTES - aggregateXmlBytes,
        );
        if (
          remainingXmlBudget <= 0 ||
          aggregateStringsCount >= MAX_AGGREGATE_STRINGS
        ) {
          aggregateCapped = true;
          const table: StringTable = {
            locale: loc,
            status: "skipped",
            strings: [],
            total_count: null,
            unparsed_count: null,
            coverage: "partial",
          };
          stringTables.push(table);
          projectedByDir.set(dirName, table);
          tableLimitations.push(
            `Projection for ${tableLabel} skipped: aggregate resource limit reached`,
          );
          continue;
        }

        const tableBudget = Math.min(STRINGS_XML_MAX_BYTES, remainingXmlBudget);
        let stringsRead: {
          text: string | null;
          truncated: boolean;
          bytesRead: number;
        };
        try {
          stringsRead = await readBoundedText(
            filePath,
            tableBudget,
            operation,
            signal,
          );
        } catch (cause) {
          if (
            cause instanceof AnalysisCancelledError ||
            signal?.aborted === true ||
            regularFileCancellation(cause) !== undefined
          ) {
            throw cause;
          }
          const readBytes =
            typeof (cause as { bytesRead?: unknown })?.bytesRead === "number"
              ? (cause as { bytesRead: number }).bytesRead
              : 0;
          aggregateXmlBytes += readBytes;
          const table: StringTable = {
            locale: loc,
            status: "malformed",
            strings: [],
            total_count: null,
            unparsed_count: null,
            coverage: "partial",
          };
          stringTables.push(table);
          projectedByDir.set(dirName, table);
          tableLimitations.push(
            `${tableLabel} could not be read: ${cause instanceof Error ? cause.message : String(cause)}`,
          );
          continue;
        }

        aggregateXmlBytes += stringsRead.bytesRead;

        if (stringsRead.text === null) {
          const table: StringTable = {
            locale: loc,
            status: "missing",
            strings: [],
            total_count: 0,
            unparsed_count: 0,
            coverage: "complete",
          };
          stringTables.push(table);
          projectedByDir.set(dirName, table);
          if (loc !== null) {
            tableLimitations.push(`No strings.xml was found for locale ${loc}`);
          } else {
            tableLimitations.push(
              "No default res/values/strings.xml was found in the decoded workspace",
            );
          }
          continue;
        }

        if (stringsRead.truncated) {
          if (tableBudget < STRINGS_XML_MAX_BYTES) {
            aggregateCapped = true;
          }
          const table: StringTable = {
            locale: loc,
            status: "oversized",
            strings: [],
            total_count: null,
            unparsed_count: null,
            coverage: "partial",
          };
          stringTables.push(table);
          projectedByDir.set(dirName, table);
          tableLimitations.push(
            loc === null
              ? `strings.xml exceeds the ${String(tableBudget)}-byte projection budget`
              : `strings.xml for locale ${loc} exceeds the ${String(tableBudget)}-byte projection budget`,
          );
          continue;
        }

        const parsed = parseDecodedStrings(stringsRead.text);
        if (parsed.malformed) {
          const table: StringTable = {
            locale: loc,
            status: "malformed",
            strings: [],
            total_count: null,
            unparsed_count: null,
            coverage: "partial",
          };
          stringTables.push(table);
          projectedByDir.set(dirName, table);
          tableLimitations.push(
            loc === null
              ? "default res/values/strings.xml is not well-formed XML"
              : `res/values-${localeQualifier(loc)}/strings.xml for locale ${loc} is not well-formed XML`,
          );
          continue;
        }

        const totalCount = parsed.entries.length;
        const remainingStringsBudget = Math.max(
          0,
          MAX_AGGREGATE_STRINGS - aggregateStringsCount,
        );
        const tableLimit = Math.min(MAX_STRINGS, remainingStringsBudget);
        const bounded = parsed.entries.slice(0, tableLimit);
        aggregateStringsCount += bounded.length;

        if (bounded.length < Math.min(totalCount, MAX_STRINGS)) {
          aggregateCapped = true;
        }

        const tableCoverage =
          totalCount > MAX_STRINGS ||
          bounded.length < totalCount ||
          parsed.unparsedCount > 0
            ? "partial"
            : "complete";

        const table: StringTable = {
          locale: loc,
          status: "present",
          strings: bounded,
          total_count: totalCount,
          unparsed_count: parsed.unparsedCount,
          coverage: tableCoverage,
        };
        stringTables.push(table);
        projectedByDir.set(dirName, table);

        if (parsed.unparsedCount > 0) {
          tableLimitations.push(
            loc === null
              ? `String entries omitted due to malformed XML or unsupported markup: ${String(parsed.unparsedCount)}`
              : `String entries omitted in locale ${loc} due to malformed XML or unsupported markup: ${String(parsed.unparsedCount)}`,
          );
        }
        if (totalCount > MAX_STRINGS) {
          tableLimitations.push(
            loc === null
              ? `strings reports the first ${String(MAX_STRINGS)} of ${String(totalCount)} entries`
              : `Locale ${loc} strings reports the first ${String(MAX_STRINGS)} of ${String(totalCount)} entries`,
          );
        } else if (bounded.length < totalCount) {
          tableLimitations.push(
            `Locale ${loc ?? "default"} strings reports ${String(bounded.length)} entries due to aggregate strings limit`,
          );
        }
      }

      let primaryStrings: Array<{ name: string; value: string }> = [];
      const primaryLocale: string | null = input.locale ?? null;
      if (input.include_strings) {
        const found = stringTables.find((t) => t.locale === primaryLocale);
        if (found) primaryStrings = found.strings;
      }

      const files = await countDecodedFiles(workspace, signal, operation);
      throwIfCancelled(operation, signal);

      const anyTablePartial = stringTables.some(
        (t) =>
          t.coverage === "partial" ||
          t.status === "oversized" ||
          t.status === "malformed" ||
          t.status === "skipped",
      );
      const coverage =
        anyTablePartial ||
        manifestRead.truncated ||
        files.capped ||
        aggregateCapped
          ? "partial"
          : "complete";
      await removeWorkspace();
      return ok(
        createAnalysisExecution(
          {
            client,
            target: { path: input.path, bytes: snapshotInfo.size, sha256 },
            metadata: {
              version_name: metadata.versionName,
              version_code: metadata.versionCode,
              min_sdk_version: metadata.minSdkVersion,
              target_sdk_version: metadata.targetSdkVersion,
              package_name: packageName,
            },
            manifest,
            strings: primaryStrings,
            locale: primaryLocale,
            locales: files.locales,
            string_tables: stringTables,
            decoded_file_count: files.count,
            coverage,
          },
          provider,
          {
            subject: { path: input.path, sha256, format: "apk" },
            limitations: [
              "Decoding skips smali (--no-src); Java-source recovery belongs to the JADX family",
              ...tableLimitations,
              ...(manifestRead.truncated
                ? [
                    `manifest is truncated at ${String(MANIFEST_MAX_BYTES)} bytes`,
                  ]
                : []),
              ...(files.capped
                ? [
                    `Decoded workspace enumeration stopped after ${String(MAX_DECODED_ENTRIES_VISITED)} entries; decoded_file_count and locales may be partial`,
                  ]
                : []),
              ...(aggregateCapped
                ? [
                    "Aggregate string table projection stopped due to resource limits",
                  ]
                : []),
              ...(cleanupFailure === null ? [] : [cleanupFailure]),
            ],
          },
        ),
      );
    } catch (cause) {
      await removeWorkspace();
      const cancellation = regularFileCancellation(cause);
      if (cancellation !== undefined)
        return err(
          failureWithCleanup(
            new AnalysisCancelledError(operation, {
              cause: cancellation.reason,
            }),
          ),
        );
      return err(
        failureWithCleanup(
          signal?.aborted === true
            ? new AnalysisCancelledError(operation, { cause })
            : sourceAdmissionFailed
              ? new AnalysisInputError(operation, { cause })
              : cause instanceof AnalysisInputError
                ? cause
                : cause instanceof AnalysisCancelledError ||
                    cause instanceof AnalysisProtocolError
                  ? cause
                  : new AnalysisProtocolError(
                      "Apktool resource projection failed",
                      {
                        cause,
                      },
                    ),
        ),
      );
    } finally {
      await source?.close().catch(() => undefined);
    }
  }
}
