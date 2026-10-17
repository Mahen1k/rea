import * as t from "@babel/types";
import { isBuiltin } from "node:module";
import { traverseJavaScriptAst } from "./javascriptSemanticTraversal.js";

import { BUILTIN_RESOURCE_METHODS } from "./javascriptBuiltinResourceMethods.js";
import type { JavaScriptModuleOrigin } from "./javascriptSemanticIr.js";
import {
  resolveSemanticBindingState,
  isUnmodifiedCommonJsWrapperBinding,
  isUnshadowedGlobal,
  commonJsWrapperBindingDeclaration,
  semanticResolutionBlocked,
  semanticStableInitializer,
  type JavaScriptSemanticAnalysisState,
} from "./javascriptSemanticState.js";
import {
  readExactJavaScriptLiteral,
  semanticStaticPropertyKey,
  unwrapJavaScriptExpression,
} from "./javascriptAstValues.js";
import {
  semanticPropertyPathKeyMatches,
  SemanticPropertyPathCoverage,
  type JavaScriptSemanticPropertyPath,
} from "./javascriptSemanticPropertyPaths.js";
import { semanticObjectPropertyReferences } from "./javascriptSemanticObjectReferences.js";
import { stringValue } from "./javascriptStaticAnalysisHelpers.js";
import {
  semanticBindingAtRead,
  semanticEffectTiming,
  semanticTopLevelEffectFollowsCapture,
} from "./javascriptSemanticMutationInitializers.js";
import { createSemanticModuleInterop } from "./javascriptModuleInterop.js";

export interface JavaScriptRequireOrigin {
  readonly origin: JavaScriptModuleOrigin;
  readonly call: t.CallExpression;
}

export type JavaScriptRequireLoaderFact =
  | "commonjs-loader"
  | "factory-loader"
  | "create-require"
  | "local"
  | "unknown";

/** Classify a bare `require(...)` using the shared lexical binding owner. */
export const semanticRequireLoaderAt = (
  node: t.CallExpression | t.OptionalCallExpression | t.NewExpression,
  state: JavaScriptSemanticAnalysisState,
  factoryBindingIds: ReadonlySet<string>,
): JavaScriptRequireLoaderFact => {
  const callee = unwrapJavaScriptExpression(node.callee).node;
  const loader = t.isIdentifier(callee, { name: "require" })
    ? callee
    : (t.isMemberExpression(callee) || t.isOptionalMemberExpression(callee)) &&
        ["resolve", "main"].includes(
          semanticStaticPropertyKey(callee.property, callee.computed) ?? "",
        ) &&
        t.isIdentifier(callee.object, { name: "require" })
      ? callee.object
      : undefined;
  if (loader === undefined) return "local";
  const binding = resolveSemanticBindingState(state, loader, "require");
  if (binding === undefined) {
    if (semanticResolutionBlocked(state, loader, "require")) return "unknown";
    return (state.ambientBindingWrites.get("require") ?? []).some(
      (write) => semanticEffectTiming(node, write, state) !== "after",
    )
      ? "unknown"
      : "commonjs-loader";
  }
  if (factoryBindingIds.has(binding.bindingId))
    return binding.initializers.length === 0 ? "factory-loader" : "unknown";
  if (
    binding.hostOrigin === "commonjs-wrapper" &&
    [...binding.declarationKinds].every((kind) => kind === "var")
  ) {
    if (binding.definitions.some(({ kind }) => kind === "function"))
      return "local";
    return commonJsWrapperBindingHasPriorWrite(node, binding, state)
      ? "unknown"
      : "commonjs-loader";
  }
  if (isWrapperRequireInitializerCall(binding, node, state))
    return "commonjs-loader";
  const wrapperBinding = commonJsWrapperBindingDeclaration(
    loader,
    "require",
    state,
  );
  if (
    wrapperBinding !== undefined &&
    !commonJsWrapperBindingHasPriorWrite(node, wrapperBinding, state)
  )
    return "commonjs-loader";
  if (isSemanticCreateRequireBinding(binding, state)) return "create-require";
  const initializer = semanticStableInitializer(binding, state)?.node;
  if (
    (binding.kind === "function" || binding.kind === "class") &&
    initializer !== undefined
  )
    return "local";
  if (
    binding.declarationKinds.size === 1 &&
    binding.declarationKinds.has("const") &&
    (t.isFunctionExpression(initializer) ||
      t.isArrowFunctionExpression(initializer))
  )
    return "local";
  return "unknown";
};

const commonJsWrapperBindingHasPriorWrite = (
  site: t.Node,
  binding: NonNullable<ReturnType<typeof resolveSemanticBindingState>>,
  state: JavaScriptSemanticAnalysisState,
): boolean => {
  const writes = state.bindingWrites.get(binding.bindingId) ?? [];
  const declarationInitializers = binding.initializers
    .map(({ node }) => node)
    .filter(
      (initializer) =>
        !writes.some((write) => semanticNodeWithin(initializer, write, state)),
    );
  return (
    writes.some(
      (write) => semanticEffectTiming(site, write, state) !== "after",
    ) ||
    declarationInitializers.some(
      (initializer) =>
        semanticEffectTiming(site, initializer, state) !== "after",
    )
  );
};

const semanticNodeWithin = (
  node: t.Node,
  ancestor: t.Node,
  state: JavaScriptSemanticAnalysisState,
): boolean => {
  let current: t.Node | undefined = node;
  while (current !== undefined) {
    if (current === ancestor) return true;
    current = state.parentsByNode.get(current);
  }
  return false;
};

/** Classify a call through an exact recovered factory-loader binding. */
export const semanticFactoryRequireLoaderAt = (
  node: t.CallExpression | t.OptionalCallExpression | t.NewExpression,
  state: JavaScriptSemanticAnalysisState,
  bindingIds: ReadonlySet<string>,
): JavaScriptRequireLoaderFact | undefined => {
  const callee = unwrapJavaScriptExpression(node.callee).node;
  if (t.isIdentifier(callee))
    return semanticFactoryLoaderMemberAt(node, state, bindingIds, null);
  if (
    (t.isMemberExpression(callee) || t.isOptionalMemberExpression(callee)) &&
    semanticStaticPropertyKey(callee.property, callee.computed) === "bind"
  )
    return semanticFactoryLoaderMemberAt(node, state, bindingIds, "bind");
  return undefined;
};

/** Classify an exact loader call by binding identity and expected member. */
export const semanticFactoryLoaderMemberAt = (
  node: t.CallExpression | t.OptionalCallExpression | t.NewExpression,
  state: JavaScriptSemanticAnalysisState,
  bindingIds: ReadonlySet<string>,
  member: string | null,
): JavaScriptRequireLoaderFact | undefined => {
  const callee = unwrapJavaScriptExpression(node.callee).node;
  let loader: t.Identifier | undefined;
  if (member === null) {
    if (t.isIdentifier(callee)) loader = callee;
  } else if (
    (t.isMemberExpression(callee) || t.isOptionalMemberExpression(callee)) &&
    semanticStaticPropertyKey(callee.property, callee.computed) === member
  ) {
    const root = unwrapJavaScriptExpression(callee.object).node;
    if (t.isIdentifier(root)) loader = root;
  }
  if (loader === undefined) return undefined;
  const binding = resolveSemanticBindingState(state, loader, loader.name);
  if (binding === undefined || !bindingIds.has(binding.bindingId))
    return undefined;
  return binding.initializers.length === 0 ? "factory-loader" : "unknown";
};

const isSemanticCreateRequireBinding = (
  binding: NonNullable<ReturnType<typeof resolveSemanticBindingState>>,
  state: JavaScriptSemanticAnalysisState,
): boolean => {
  if (binding.initializers.length !== 1) return false;
  const initializer = semanticStableInitializer(binding, state)?.node;
  if (!t.isCallExpression(initializer)) return false;
  const callee = unwrapJavaScriptExpression(initializer.callee).node;
  if (t.isIdentifier(callee)) {
    const origins = resolveSemanticBindingState(
      state,
      callee,
      callee.name,
    )?.directOrigins;
    if (origins?.length !== 1) return false;
    const [origin] = origins;
    return (
      origin?.importedPath.at(-1) === "createRequire" &&
      ["module", "node:module"].includes(origin.specifier)
    );
  }
  const chain = semanticMemberChain(callee);
  if (chain === undefined || chain.members.at(-1) !== "createRequire")
    return false;
  if (!t.isNode(chain.root)) return false;
  const root = unwrapJavaScriptExpression(chain.root).node;
  if (!t.isIdentifier(root)) return false;
  const origins = resolveSemanticBindingState(
    state,
    root,
    root.name,
  )?.directOrigins;
  if (origins?.length !== 1) return false;
  const [origin] = origins;
  return (
    origin?.importedPath.length === 0 &&
    ["module", "node:module"].includes(origin.specifier)
  );
};

/** The RHS call runs before its assignment replaces Node's wrapper loader. */
const isWrapperRequireInitializerCall = (
  binding: NonNullable<ReturnType<typeof resolveSemanticBindingState>>,
  node: t.CallExpression | t.OptionalCallExpression | t.NewExpression,
  state: JavaScriptSemanticAnalysisState,
): boolean => {
  const scope = state.scopesById.get(binding.scopeId);
  if (
    scope?.kind !== "program" ||
    binding.kind !== "variable" ||
    binding.declarationKinds.size !== 1 ||
    !binding.declarationKinds.has("var") ||
    binding.initializers.length !== 1 ||
    binding.initializers[0]?.node !== node
  )
    return false;
  const assignment = state.parentsByNode.get(node);
  if (
    !t.isAssignmentExpression(assignment) ||
    assignment.right !== node ||
    state.conditionallySkippedExpressions.has(node)
  )
    return false;
  const statement = state.parentsByNode.get(assignment);
  if (!t.isExpressionStatement(statement)) return false;
  if (state.parentsByNode.get(statement) !== state.program) return false;
  const target = unwrapJavaScriptExpression(assignment.left).node;
  return (
    t.isIdentifier(target, { name: "require" }) &&
    resolveSemanticBindingState(state, target, target.name) === binding
  );
};

// Ambient indexing finishes before these derived facts are consumed. Keep only
// replacement sites, rather than rescanning unrelated global member writes.
const globalProcessReplacements = new WeakMap<
  JavaScriptSemanticAnalysisState,
  readonly (t.Node | undefined)[]
>();
const moduleRequireWrites = new WeakMap<
  JavaScriptSemanticAnalysisState,
  readonly t.Node[]
>();

/** Member collection can discover stored module exposure after an earlier query. */
export const clearSemanticRequireWriteCache = (
  state: JavaScriptSemanticAnalysisState,
): void => {
  moduleRequireWrites.delete(state);
};

/** Resolve the CommonJS wrapper module identity through ordered aliases. */
export const semanticCommonJsModuleObjectAt = (
  node: t.Node,
  state: JavaScriptSemanticAnalysisState,
  visited = new Set<string>(),
): boolean => {
  const value = unwrapJavaScriptExpression(node).node;
  if (!t.isIdentifier(value)) return false;
  if (value.name === "module")
    return resolveSemanticBindingState(state, value, "module") === undefined
      ? !semanticResolutionBlocked(state, value, "module")
      : isUnmodifiedCommonJsWrapperBinding(value, "module", state);
  const binding = resolveSemanticBindingState(state, value, value.name);
  if (binding === undefined || visited.has(binding.bindingId)) return false;
  const next = new Set(visited).add(binding.bindingId);
  const { initializers } = semanticBindingAtRead(
    binding,
    value,
    state.parentsByNode,
  ).binding;
  return (
    initializers.length > 0 &&
    initializers.every(
      ({ node: init, projection }) =>
        projection.length === 0 &&
        semanticCommonJsModuleObjectAt(init, state, next),
    )
  );
};

const writesModuleRequire = (
  state: JavaScriptSemanticAnalysisState,
): readonly t.Node[] => {
  const cached = moduleRequireWrites.get(state);
  if (cached !== undefined) return cached;
  // Interop invocation resolution may ask for require provenance while this
  // index is being built. Publish a temporary empty result to break that cycle.
  moduleRequireWrites.set(state, []);
  const writes: t.Node[] = [];
  const interop = createSemanticModuleInterop(state);
  const isSeparateReceiver = (
    node: t.Node,
    visited = new Set<string>(),
  ): boolean => {
    const value = unwrapJavaScriptExpression(node).node;
    if (
      interop.isFreshObject(value) ||
      readExactJavaScriptLiteral(value).found ||
      t.isBigIntLiteral(value) ||
      t.isUnaryExpression(value) ||
      isUnshadowedGlobal(value, state, "undefined")
    )
      return true;
    const separateNamespace = (origin: JavaScriptModuleOrigin): boolean =>
      isBuiltin(origin.specifier) &&
      (origin.importedPath.length === 0 ||
        (origin.resolutionMode !== "require" &&
          origin.importedPath.length === 1 &&
          origin.importedPath[0] === "default"));
    const required = semanticRequireOrigin(value, state);
    if (required !== undefined && separateNamespace(required.origin))
      return true;
    if (!t.isIdentifier(value)) return false;
    const binding = resolveSemanticBindingState(state, value, value.name);
    if (binding === undefined || visited.has(binding.bindingId)) return false;
    const snapshot = semanticBindingAtRead(binding, value, state.parentsByNode);
    if (snapshot.status !== "ordered") return false;
    const { initializers, referenceInitializers, directOrigins } =
      snapshot.binding;
    if (referenceInitializers.length !== 0) return false;
    if (initializers.length === 0)
      return directOrigins.length > 0 && directOrigins.every(separateNamespace);
    const next = new Set(visited).add(binding.bindingId);
    return initializers.every(
      ({ node: source, projection }) =>
        projection.length === 0 && isSeparateReceiver(source, next),
    );
  };
  // Unknown keys, spread sources and accessors may all replace the delegate.
  const mayContainRequire = (source: t.Node | undefined): boolean =>
    !t.isObjectExpression(source) ||
    source.properties.some((property) => {
      if (t.isSpreadElement(property)) return true;
      const key = semanticStaticPropertyKey(property.key, property.computed);
      return key === null || key === "require";
    });
  // This index is built over a completed binding/ambient-write snapshot. Cache
  // only fully explored module-free node/projection pairs; a partial walk that
  // found exposure cannot establish anything about its other visited nodes.
  const moduleFree = new WeakMap<t.Node, SemanticPropertyPathCoverage>();
  const plainObject = (
    source: t.Node | undefined,
    seen = new Set<string>(),
  ): t.ObjectExpression | undefined => {
    if (source === undefined) return undefined;
    const value = unwrapJavaScriptExpression(source).node;
    if (t.isObjectExpression(value))
      return value.properties.every(t.isObjectProperty) ? value : undefined;
    if (!t.isIdentifier(value)) return undefined;
    const binding = resolveSemanticBindingState(state, value, value.name);
    if (
      binding === undefined ||
      seen.has(binding.bindingId) ||
      binding.memberWrites.length > 0 ||
      binding.escapedPaths.length > 0
    )
      return undefined;
    const initializer = semanticStableInitializer(binding, state);
    return initializer?.projection.length === 0
      ? plainObject(initializer.node, new Set(seen).add(binding.bindingId))
      : undefined;
  };
  // Member effects already own aliases, selected paths and ordering. Follow
  // their assigned values instead of treating every write as the wrapper.
  // Accessors and unproven descriptor/source maps remain conservative.
  const writtenValues = (
    mutation: t.Node | undefined,
    key: string,
  ):
    | readonly { node: t.Node; path: JavaScriptSemanticPropertyPath }[]
    | undefined => {
    if (t.isAssignmentExpression(mutation))
      return ["=", "||=", "&&=", "??="].includes(mutation.operator)
        ? [{ node: mutation.right, path: [] }]
        : undefined;
    if (!t.isCallExpression(mutation) && !t.isOptionalCallExpression(mutation))
      return undefined;
    const invocation = interop.intrinsicInvocation(mutation);
    const args = invocation?.arguments;
    if (
      invocation?.kind !== "known" ||
      args === undefined ||
      args.some(t.isSpreadElement)
    )
      return undefined;
    const operation = invocation.path.join(".");
    if (operation === "intrinsic.Reflect.set" && args[2] !== undefined)
      return [{ node: args[2], path: [] }];
    if (operation === "intrinsic.Object.assign")
      return args.slice(1).every((source) => plainObject(source) !== undefined)
        ? args.slice(1).map((node) => ({ node, path: [key] }))
        : undefined;
    let descriptor: t.Node | undefined;
    if (operation === "intrinsic.Object.defineProperties") {
      const properties = plainObject(args[1]);
      if (
        properties?.properties.some(
          (property) =>
            !t.isObjectProperty(property) ||
            semanticStaticPropertyKey(property.key, property.computed) === null,
        )
      )
        return undefined;
      const selected = properties?.properties.findLast(
        (property) =>
          t.isObjectProperty(property) &&
          semanticStaticPropertyKey(property.key, property.computed) === key,
      );
      if (t.isObjectProperty(selected)) descriptor = selected.value;
    } else if (
      [
        "intrinsic.Object.defineProperty",
        "intrinsic.Reflect.defineProperty",
      ].includes(operation)
    )
      descriptor = args[2];
    const data = plainObject(descriptor);
    if (
      data === undefined ||
      !data.properties.every(
        (property) =>
          t.isObjectProperty(property) &&
          ["value", "writable", "enumerable", "configurable"].includes(
            semanticStaticPropertyKey(property.key, property.computed) ?? "",
          ),
      )
    )
      return undefined;
    return [{ node: data, path: ["value"] }];
  };
  const exposesModule = (nodes: readonly t.Node[], call: t.Node): boolean => {
    const pending: {
      node: t.Node;
      path: JavaScriptSemanticPropertyPath;
      readAt?: t.Node;
      // Discharging a recorded write requires a positive module-free proof;
      // unknown call results and closures must retain the original uncertainty.
      written?: true;
    }[] = nodes.map((node) => ({ node, path: [] }));
    const visited = new WeakMap<
      t.Node,
      Map<t.Node, SemanticPropertyPathCoverage>
    >();
    const writtenVisited = new WeakMap<
      t.Node,
      Map<t.Node, SemanticPropertyPathCoverage>
    >();
    let timeDependent = false;
    const examined: { node: t.Node; path: JavaScriptSemanticPropertyPath }[] =
      [];
    while (pending.length > 0) {
      const {
        node: source,
        path,
        readAt: capturedAt,
        written,
      } = pending.pop()!;
      const value = unwrapJavaScriptExpression(source).node;
      const readAt = capturedAt ?? value;
      const traversal = written ? writtenVisited : visited;
      const captures =
        traversal.get(value) ?? new Map<t.Node, SemanticPropertyPathCoverage>();
      const coverage =
        captures.get(readAt) ?? new SemanticPropertyPathCoverage();
      if (coverage.covers(path)) continue;
      coverage.retain(path);
      captures.set(readAt, coverage);
      traversal.set(value, captures);
      const binding = t.isIdentifier(value)
        ? resolveSemanticBindingState(state, value, value.name)
        : undefined;
      for (const effect of binding?.memberWrites ?? []) {
        if (
          !effect.path.slice(0, path.length).every((key, index) => {
            const selected = path[index];
            return (
              selected === null ||
              typeof selected === "object" ||
              semanticPropertyPathKeyMatches(key, String(selected))
            );
          })
        )
          continue;
        // A saved object remains shared; a saved property value retains its
        // earlier capture. Such timing-dependent proofs cannot be reused at
        // another alias use merely because they reached the same initializer.
        timeDependent = true;
        if (
          effect.node !== call &&
          effect.node !== state.parentsByNode.get(readAt) &&
          semanticEffectTiming(readAt, effect.node, state) !== "after"
        ) {
          const key = effect.path.at(-1);
          const values =
            effect.path.every((part) => typeof part === "string") &&
            typeof key === "string"
              ? writtenValues(effect.node, key)
              : undefined;
          if (values === undefined) return true;
          for (const reference of values)
            pending.push({
              node: reference.node,
              path: [...reference.path, ...path.slice(effect.path.length)],
              readAt,
              written: true,
            });
        }
      }
      if (!written && moduleFree.get(value)?.covers(path)) continue;
      examined.push({ node: value, path });
      for (const reference of interop.intrinsicValueReferences(value))
        pending.push({
          node: reference.node,
          path: [...reference.path, ...path],
          readAt: reference.node,
          ...(written ? { written } : {}),
        });
      if (semanticCommonJsModuleObjectAt(value, state)) {
        if (path.length === 0) return true;
        const first = path[0];
        if (
          typeof first === "string" &&
          ["id", "filename", "loaded"].includes(first) &&
          !state.ambientWrites.covers(["commonjs-module", first])
        )
          continue;
        return true;
      }
      if (t.isIdentifier(value)) {
        if (
          written &&
          (binding === undefined || binding.initializers.length === 0) &&
          !isUnshadowedGlobal(value, state, "undefined")
        )
          return true;
        if (binding !== undefined) {
          // Initializers do not prove a subsequently changed property module-free.
          // Consume the alias-aware effect owner, preserving unrelated slots,
          // earlier saved values and the current call's own argument exposure.
          for (const initializer of semanticBindingAtRead(
            binding,
            value,
            state.parentsByNode,
          ).binding.initializers)
            pending.push({
              node: initializer.node,
              readAt:
                initializer.projection.length > 0 && path.length === 0
                  ? initializer.node
                  : readAt,
              path: [
                ...initializer.projection.map((key) =>
                  key === null ? null : String(key),
                ),
                ...path,
              ],
              ...(written ? { written } : {}),
            });
        }
      } else if (t.isSpreadElement(value))
        pending.push({
          node: value.argument,
          path,
          readAt,
          ...(written ? { written } : {}),
        });
      else if (t.isArrayExpression(value)) {
        const [key, ...remaining] = path;
        const shifted = value.elements.some(t.isSpreadElement);
        for (let index = 0; index < value.elements.length; index++) {
          const element = value.elements[index];
          if (
            element !== null &&
            element !== undefined &&
            (key === undefined ||
              shifted ||
              semanticPropertyPathKeyMatches(key, String(index)) ||
              t.isSpreadElement(element))
          )
            pending.push({
              node: element,
              path: key === undefined ? [] : remaining,
              readAt,
              ...(written ? { written } : {}),
            });
        }
      } else if (t.isObjectExpression(value)) {
        pending.push(
          ...semanticObjectPropertyReferences(value, path, state).map(
            (reference) => ({
              ...reference,
              readAt,
              ...(written ? { written } : {}),
            }),
          ),
        );
      } else if (
        t.isMemberExpression(value) ||
        t.isOptionalMemberExpression(value)
      ) {
        pending.push({
          node: value.object,
          readAt: path.length === 0 ? value : readAt,
          path: [
            semanticStaticPropertyKey(value.property, value.computed),
            ...path,
          ],
          ...(written ? { written } : {}),
        });
      } else if (
        t.isConditionalExpression(value) ||
        t.isLogicalExpression(value)
      ) {
        pending.push(
          {
            node: t.isConditionalExpression(value)
              ? value.consequent
              : value.left,
            path,
            readAt,
            ...(written ? { written } : {}),
          },
          {
            node: t.isConditionalExpression(value)
              ? value.alternate
              : value.right,
            path,
            readAt,
            ...(written ? { written } : {}),
          },
        );
      } else if (t.isSequenceExpression(value)) {
        const last = value.expressions.at(-1);
        if (last !== undefined)
          pending.push({
            node: last,
            path,
            readAt,
            ...(written ? { written } : {}),
          });
      } else if (t.isAssignmentExpression(value)) {
        if (["=", "||=", "&&=", "??="].includes(value.operator))
          pending.push({
            node: value.right,
            path,
            readAt,
            ...(written ? { written } : {}),
          });
        if (["||=", "&&=", "??="].includes(value.operator))
          pending.push({
            node: value.left,
            path,
            readAt,
            ...(written ? { written } : {}),
          });
      } else if (
        t.isCallExpression(value) ||
        t.isOptionalCallExpression(value)
      ) {
        if (written) return true;
        pending.push(
          ...value.arguments.map((node) => ({ node, path: [], readAt })),
        );
      } else if (
        written &&
        !readExactJavaScriptLiteral(value).found &&
        !t.isUnaryExpression(value) &&
        !t.isBinaryExpression(value) &&
        !t.isTemplateLiteral(value) &&
        !t.isUpdateExpression(value)
      )
        return true;
    }
    if (timeDependent) return false;
    for (const { node, path } of examined) {
      const coverage =
        moduleFree.get(node) ?? new SemanticPropertyPathCoverage();
      coverage.retain(path);
      moduleFree.set(node, coverage);
    }
    return false;
  };
  traverseJavaScriptAst(state.program, {
    enter: (node) => {
      const target = t.isAssignmentExpression(node)
        ? node.left
        : t.isUpdateExpression(node) ||
            t.isUnaryExpression(node, { operator: "delete" })
          ? node.argument
          : undefined;
      if (target !== undefined) {
        const members: string[] = [];
        let root: t.Node = target;
        while (
          t.isMemberExpression(root) ||
          t.isOptionalMemberExpression(root)
        ) {
          const key = semanticStaticPropertyKey(root.property, root.computed);
          if (key === null) break;
          members.unshift(key);
          root = root.object;
        }
        if (
          members.length === 1 &&
          members[0] === "require" &&
          semanticCommonJsModuleObjectAt(root, state)
        )
          writes.push(node);
        else if (
          members.length === 0 &&
          (t.isMemberExpression(target) ||
            t.isOptionalMemberExpression(target)) &&
          target.computed &&
          semanticStaticPropertyKey(target.property, true) === null &&
          semanticCommonJsModuleObjectAt(target.object, state)
        )
          // An unknown computed key may be "require"; retain uncertainty rather
          // than treating this direct delegate write as a proven unrelated slot.
          writes.push(node);
      }
      if (t.isCallExpression(node) || t.isOptionalCallExpression(node)) {
        const invocation = interop.intrinsicInvocation(node);
        if (
          invocation?.kind === "opaque" &&
          ((invocation.path[1] === "Object" &&
            ["assign", "defineProperty", "defineProperties"].includes(
              invocation.path[2] ?? "",
            )) ||
            (invocation.path[1] === "Reflect" &&
              invocation.path[2] === "set")) &&
          invocation.path.at(-1) !== "bind"
        ) {
          // An overwritten callable does not retain native mutator argument
          // semantics. Preserve any module reference supplied directly,
          // through call/apply containers or a captured bound argument.
          if (exposesModule([...node.arguments, node.callee], node))
            writes.push(node);
          return;
        }
        const owner =
          invocation?.path?.length === 3 ? invocation.path[1] : undefined;
        const method = invocation?.path?.at(-1);
        const args = invocation?.arguments;
        if (
          (owner === "Object" || owner === "Reflect") &&
          method === "defineProperty" &&
          semanticCommonJsModuleObjectAt(args?.[0] ?? t.nullLiteral(), state)
        ) {
          const key = interop.staticPropertyKey(args?.[1]);
          if (key === "require" || key === undefined) writes.push(node);
        } else if (owner === "Reflect" && method === "set") {
          const key = args?.slice(0, 2).some(t.isSpreadElement)
            ? undefined
            : args !== undefined && args.length < 2
              ? "undefined"
              : interop.staticPropertyKey(args?.[1]);
          if (key !== "require" && key !== undefined) return;
          // Ordinary [[Set]] writes the receiver, which defaults to the target
          // only when omitted. An unknown receiver can still be this module.
          const receiver =
            args !== undefined && args.length >= 4 ? args[3] : args?.[0];
          if (
            receiver === undefined ||
            args?.slice(0, 4).some(t.isSpreadElement)
          ) {
            writes.push(node);
            return;
          }
          if (!isSeparateReceiver(receiver)) writes.push(node);
        } else if (
          owner === "Object" &&
          method === "defineProperties" &&
          semanticCommonJsModuleObjectAt(args?.[0] ?? t.nullLiteral(), state)
        ) {
          const descriptors = args?.[1];
          if (mayContainRequire(descriptors)) writes.push(node);
        } else if (
          owner === "Object" &&
          method === "assign" &&
          semanticCommonJsModuleObjectAt(args?.[0] ?? t.nullLiteral(), state)
        ) {
          if (args?.slice(1).some(mayContainRequire)) writes.push(node);
        }
      }
    },
  });
  moduleRequireWrites.set(state, writes);
  return writes;
};

/** Whether the original global process object can still own effects at this source site. */
export const semanticOriginalGlobalProcessAt = (
  node: t.Node,
  state: JavaScriptSemanticAnalysisState,
): boolean => {
  let replacements = globalProcessReplacements.get(state);
  if (replacements === undefined) {
    replacements = [
      ...state.ambientWriteEffects
        .filter(
          ({ path }) =>
            path.length <= 2 &&
            path.every((key, index) =>
              semanticPropertyPathKeyMatches(
                key,
                ["global", "process"][index]!,
              ),
            ),
        )
        .map(({ node: write }) => write),
      ...(state.ambientBindingWrites.get("process") ?? []),
    ];
    globalProcessReplacements.set(state, replacements);
  }
  return !replacements.some(
    (write) =>
      !semanticTopLevelEffectFollowsCapture(node, write, state.parentsByNode),
  );
};

/** Node's unbound process reference shares the cached process exports object. */
export const semanticGlobalProcessOrigin = (
  node: t.Node,
  state: JavaScriptSemanticAnalysisState,
): JavaScriptModuleOrigin | undefined =>
  t.isIdentifier(node, { name: "process" }) &&
  resolveSemanticBindingState(state, node, "process") === undefined &&
  !semanticResolutionBlocked(state, node, "process") &&
  semanticOriginalGlobalProcessAt(node, state)
    ? { specifier: "node:process", importedPath: [], resolutionMode: "require" }
    : undefined;

/** Resolve qualified global-object process references, preserving their selected path. */
export const semanticGlobalProcessPathOrigin = (
  node: t.Node,
  state: JavaScriptSemanticAnalysisState,
): JavaScriptModuleOrigin | undefined => {
  const members: string[] = [];
  let current = unwrapJavaScriptExpression(node).node;
  while (
    t.isMemberExpression(current) ||
    t.isOptionalMemberExpression(current)
  ) {
    const key = semanticStaticPropertyKey(current.property, current.computed);
    if (key === null) return undefined;
    members.unshift(key);
    current = unwrapJavaScriptExpression(current.object).node;
  }
  if (
    !t.isIdentifier(current) ||
    !["globalThis", "global", "window", "self"].includes(current.name) ||
    resolveSemanticBindingState(state, current, current.name) !== undefined ||
    semanticResolutionBlocked(state, current, current.name) ||
    members[0] !== "process" ||
    !semanticOriginalGlobalProcessAt(node, state)
  )
    return undefined;
  return {
    specifier: "node:process",
    importedPath: members.slice(1),
    resolutionMode: "require",
  };
};

/** Strip a static member chain, returning its root expression and member path. */
export const semanticMemberChain = (
  node: t.Node | null | undefined,
):
  | { readonly root: t.Node | null | undefined; readonly members: string[] }
  | undefined => {
  const members: string[] = [];
  let current = node;
  while (current !== null && current !== undefined) {
    current = unwrapJavaScriptExpression(current).node;
    if (
      !t.isMemberExpression(current) &&
      !t.isOptionalMemberExpression(current)
    )
      break;
    const member = semanticStaticPropertyKey(
      current.property,
      current.computed,
    );
    if (member === null || !t.isNode(current.object)) return undefined;
    members.push(member);
    current = current.object;
  }
  return { root: current, members: members.reverse() };
};

/** Recover an unshadowed literal require origin and its exact member path. */
export const semanticRequireOrigin = (
  node: t.Node | null | undefined,
  state: JavaScriptSemanticAnalysisState,
): JavaScriptRequireOrigin | undefined => {
  const chain = semanticMemberChain(node);
  const current = chain?.root;
  if (
    chain === undefined ||
    !t.isCallExpression(current) ||
    !t.isIdentifier(current.callee, { name: "require" })
  )
    return undefined;
  if (
    writesModuleRequire(state).some(
      (write) =>
        !semanticTopLevelEffectFollowsCapture(
          current,
          write,
          state.parentsByNode,
        ),
    )
  )
    return undefined;
  const requireBinding = resolveSemanticBindingState(
    state,
    current.callee,
    "require",
  );
  if (
    (requireBinding !== undefined &&
      !isUnmodifiedCommonJsWrapperBinding(current.callee, "require", state) &&
      !isWrapperRequireInitializerCall(requireBinding, current, state)) ||
    (requireBinding === undefined &&
      semanticResolutionBlocked(state, current.callee, "require")) ||
    (state.ambientBindingWrites.get("require") ?? []).some(
      (write) =>
        !semanticTopLevelEffectFollowsCapture(
          current,
          write,
          state.parentsByNode,
        ),
    )
  )
    return undefined;
  const specifier = stringValue(current.arguments[0]);
  return specifier === undefined
    ? undefined
    : {
        origin: {
          specifier,
          importedPath: chain.members,
          resolutionMode: "require",
        },
        call: current,
      };
};

/** Node's fs.promises export and fs/promises require share one object. */
export const semanticRequireExportsIdentity = <Key>(
  specifier: string,
  path: readonly Key[],
): { readonly specifier: string; readonly path: readonly (Key | string)[] } => {
  const name = specifier.replace(/^node:/u, "");
  if (name === "fs/promises") return { specifier: name, path };
  return name === "fs" && path[0] === "promises" && path.length > 1
    ? { specifier: "fs/promises", path: path.slice(1) }
    : { specifier: name, path };
};

const MUTABLE_BUILTIN_DEFAULTS = new Set([
  ...Object.keys(BUILTIN_RESOURCE_METHODS),
  "http",
  "https",
  "child_process",
  "timers",
  "process",
]);

/** Known Node namespaces have native descriptors; external exports do not. */
export const semanticBuiltinNamespace = (
  origin: JavaScriptModuleOrigin,
): boolean => {
  const path =
    origin.resolutionMode !== "require" && origin.importedPath[0] === "default"
      ? origin.importedPath.slice(1)
      : origin.importedPath;
  const shared = semanticRequireExportsIdentity(origin.specifier, path);
  return (
    shared.path.length === 0 && MUTABLE_BUILTIN_DEFAULTS.has(shared.specifier)
  );
};

/** Mutable default/object selections share CommonJS identity; namespace slots do not. */
export const semanticMutableBuiltinOrigin = <Key = never>(
  origin: JavaScriptModuleOrigin,
  selected: readonly Key[] = [],
):
  | { readonly specifier: string; readonly path: readonly (Key | string)[] }
  | undefined => {
  const path = [...origin.importedPath, ...selected];
  if (origin.resolutionMode === "require")
    return { specifier: origin.specifier, path };
  const specifier = origin.specifier.replace(/^node:/u, "");
  if (!MUTABLE_BUILTIN_DEFAULTS.has(specifier)) return undefined;
  if (path[0] === "default") return { specifier, path: path.slice(1) };
  if (specifier === "process" && (path[0] === "env" || path[0] === "argv"))
    return { specifier, path };
  return specifier === "fs" && path[0] === "promises"
    ? { specifier, path }
    : undefined;
};
