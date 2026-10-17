import * as t from "@babel/types";

import {
  semanticStaticPropertyKey,
  semanticWriteTargetsSteps,
  unwrapJavaScriptExpression,
} from "./javascriptAstValues.js";
import {
  resolveSemanticBindingState,
  type JavaScriptSemanticAnalysisState,
  type JavaScriptSemanticBindingState,
} from "./javascriptSemanticState.js";
import type { JavaScriptIntrinsicInvocation } from "./javascriptElectronMemberWrites.js";
import { isJavaScriptViteDefaultUndefined } from "./javascriptViteHelper.js";

import {
  FOREIGN,
  UNKNOWN,
  type ViteCacheAllocation,
  type ViteCacheIdentity,
  type ViteCacheWrite,
  type Vertex,
  type VertexKey,
  type Input,
} from "./javascriptViteCacheIdentityTypes.js";
import {
  ViteCacheProperties,
  viteCacheObjectOperation,
} from "./javascriptViteCacheProperties.js";
type Key = string | null;
type DefaultInput = Extract<Input, { kind: "default" }>;

const providedDefaultInput = (
  input: DefaultInput,
  source: ViteCacheIdentity | undefined,
): boolean =>
  input.defined ||
  (source?.allocation != null && source.allocation.kind !== "foreign");

const OBJECT_TARGET_RESULTS = new Set([
  "assign",
  "defineProperty",
  "defineProperties",
  "setPrototypeOf",
  "freeze",
  "seal",
  "preventExtensions",
]);

const joinOwner = (
  left: ViteCacheIdentity["owner"],
  right: ViteCacheIdentity["owner"],
): ViteCacheIdentity["owner"] =>
  left === undefined
    ? right
    : right === undefined || left === right
      ? left
      : null;

const joinIdentity = (
  left: ViteCacheIdentity | undefined,
  right: ViteCacheIdentity,
): ViteCacheIdentity => {
  if (left === undefined) return right;
  const allocation =
    left.allocation === right.allocation ? left.allocation : null;
  const owner = joinOwner(left.owner, right.owner);
  const children = joinOwner(left.children, right.children);
  return allocation === left.allocation &&
    owner === left.owner &&
    children === left.children
    ? left
    : { allocation, owner, children };
};

/** normalize expressions once; joins never retain a helper-owner set per alias. */
export class ViteCacheIdentities {
  private readonly vertices = new Map<VertexKey, Vertex>();
  private readonly normalizeQueue: t.Node[] = [];
  private readonly allocations = new Map<string, Vertex>();
  private readonly cacheInitializations = new WeakSet<t.Node>();
  private readonly helperResults = new WeakMap<
    t.CallExpression | t.OptionalCallExpression,
    Vertex
  >();
  private readonly defaultChoices: { target: Vertex; input: DefaultInput }[] =
    [];
  private readonly helperArgumentReads = new WeakMap<
    t.CallExpression | t.OptionalCallExpression,
    {
      readonly freshIndexes: boolean;
      readonly table: t.Node | undefined;
      readonly mapper: t.Node | undefined;
      readonly providedTable: DefaultInput | undefined;
      readonly mapperTable: Vertex | undefined;
    }
  >();
  ambiguousCacheFamily = false;
  private readonly reads = new Map<Vertex, Map<Key, Map<t.Node, Vertex>>>();
  private readonly pending: Vertex[] = [];
  private readonly queued = new Set<Vertex>();
  private readonly allocationVertices = new Map<ViteCacheAllocation, Vertex>();
  private snapshots = false;
  private readonly writeReceivers = new Map<Vertex, ViteCacheWrite[]>();
  private readonly retainedWrites = new Map<
    ViteCacheWrite,
    ViteCacheAllocation
  >();

  private readonly properties: ViteCacheProperties;
  constructor(
    private readonly state: JavaScriptSemanticAnalysisState,
    private readonly invocation: (
      node: t.CallExpression | t.OptionalCallExpression,
    ) => JavaScriptIntrinsicInvocation | undefined,
  ) {
    this.properties = new ViteCacheProperties(state, {
      vertex: () => this.vertex({}),
      normalize: (node) => this.normalize(node),
      project: (source, path, read) => this.project(source, path, read),
      connect: (target, input) => this.connect(target, input),
      enqueue: (vertex) => this.enqueue(vertex),
      objectCall: (node) => viteCacheObjectOperation(node, this.invocation),
      objectArguments: (node) => this.invocation(node)?.arguments,
      invocation: this.invocation,
    });
  }

  read(node: t.Node): ViteCacheIdentity | undefined {
    return this.vertices.get(node)?.fact;
  }

  /** Parsed call facts distinguish read-only parameters from opaque calls. */
  readOnlyHelperArguments(
    call: t.CallExpression | t.OptionalCallExpression,
  ): readonly t.Node[] {
    const proof = this.helperArgumentReads.get(call);
    if (
      proof === undefined ||
      !proof.freshIndexes ||
      this.read(call.callee)?.allocation?.kind !== "helper"
    )
      return [];
    const reads: t.Node[] = [];
    // A mapped argument is read by value only when its proven container holds
    // plain data slots; accessors and spreads can hide unexamined writes.
    if (proof.table !== undefined && this.plainDataSlots(proof.table))
      reads.push(proof.table);
    const tableAllocation = proof.mapperTable?.fact?.allocation;
    const provided = proof.providedTable;
    if (
      proof.mapper !== undefined &&
      ((provided !== undefined &&
        providedDefaultInput(provided, provided.source.fact)) ||
        (tableAllocation != null &&
          tableAllocation.kind !== "foreign" &&
          this.plainDataSlots(proof.mapper)))
    )
      reads.push(proof.mapper);
    return reads;
  }

  /**
   * An unproven indexes protocol runs the mapped reads through arbitrary code.
   * Returns the helper's cache table node to expose for such a call when the
   * selected table can include the cache: a supplied table argument selects
   * that table alone, and a supplied mapper keeps the cache out while its f
   * slot is proven present and truthy.
   */
  helperMappedTableEscape(
    call: t.CallExpression | t.OptionalCallExpression,
  ): t.Node | undefined {
    const indexes = call.arguments[0];
    const selection =
      indexes === undefined
        ? undefined
        : unwrapJavaScriptExpression(indexes).node;
    if (t.isArrayExpression(selection)) return undefined;
    const owner = this.read(call.callee)?.owner;
    if (typeof owner !== "string") return undefined;
    const usesDefault = (node: t.Node | undefined): boolean =>
      node === undefined || isJavaScriptViteDefaultUndefined(node, this.state);
    const tableArgument = call.arguments[2];
    if (tableArgument !== undefined && !usesDefault(tableArgument))
      return undefined;
    const mapperArgument = call.arguments[1];
    if (
      mapperArgument !== undefined &&
      !usesDefault(mapperArgument) &&
      this.provesMapperSelectedTable(
        unwrapJavaScriptExpression(mapperArgument).node,
      )
    )
      return undefined;
    return this.allocations.get(owner)?.seed?.allocation?.node;
  }

  /** Only array or plain data object literals keep mapped reads free of getters. */
  private plainDataSlots(argument: t.Node | undefined): boolean {
    if (argument === undefined) return false;
    const node = this.read(argument)?.allocation?.node;
    if (t.isArrayExpression(node)) return true;
    if (!t.isObjectExpression(node)) return false;
    return node.properties.every(
      (property) =>
        t.isObjectProperty(property) &&
        !property.computed &&
        !(
          t.isIdentifier(property.key, { name: "__proto__" }) ||
          t.isStringLiteral(property.key, { value: "__proto__" })
        ),
    );
  }

  /**
   * Whether a supplied mapper keeps mapped reads on its own table: its f slot
   * must be proven present and truthy, and no later spread may redefine it.
   */
  private provesMapperSelectedTable(mapper: t.Node): boolean {
    if (!t.isObjectExpression(mapper)) return false;
    let found = false;
    for (const property of mapper.properties) {
      if (t.isSpreadElement(property)) {
        if (found) return false;
        continue;
      }
      if (
        !t.isObjectProperty(property) ||
        property.computed ||
        property.shorthand ||
        !(
          t.isIdentifier(property.key, { name: "f" }) ||
          t.isStringLiteral(property.key, { value: "f" })
        )
      )
        continue;
      // Duplicate keys resolve to the last value.
      if (found) return false;
      found = this.provesTruthySlot(property.value);
    }
    return found;
  }

  /** Whether a property value is proven defined with a truthy plain value. */
  private provesTruthySlot(node: t.Node): boolean {
    return (
      t.isArrayExpression(node) ||
      t.isObjectExpression(node) ||
      t.isFunction(node) ||
      (t.isLiteral(node) &&
        ((t.isBooleanLiteral(node) && node.value) ||
          (t.isStringLiteral(node) && node.value.length > 0) ||
          (t.isNumericLiteral(node) &&
            node.value !== 0 &&
            !Number.isNaN(node.value)) ||
          t.isRegExpLiteral(node)))
    );
  }

  /** propagate unexamined exposure through normalized aliases and contained values. */
  *escapedAllocationsSteps(
    nodes: readonly t.Node[],
  ): Generator<void, ReadonlySet<ViteCacheAllocation>> {
    const allocations = new Set<ViteCacheAllocation>();
    const seen = new Set<Vertex>();
    const pending: Vertex[] = [];
    let examined = 0;
    const retain = (vertex: Vertex): void => {
      if (!seen.has(vertex)) {
        seen.add(vertex);
        pending.push(vertex);
      }
    };
    for (const node of nodes) {
      if (examined++ % 1024 === 0) yield;
      const vertex = this.vertices.get(node);
      if (vertex !== undefined) retain(vertex);
    }
    for (let index = 0; index < pending.length; index++) {
      if (examined++ % 1024 === 0) yield;
      const vertex = pending[index];
      if (vertex === undefined) continue;
      if (vertex.fact?.allocation != null)
        allocations.add(vertex.fact.allocation);
      for (const input of vertex.inputs) {
        if (examined++ % 1024 === 0) yield;
        retain(input.source);
        if (
          input.kind === "default" &&
          !providedDefaultInput(input, input.source.fact)
        )
          retain(input.fallback);
      }
    }
    return allocations;
  }

  normalize(node: t.Node): Vertex {
    const previous = this.vertices.get(node);
    if (previous !== undefined) return previous;
    const vertex = this.vertex(node);
    this.normalizeQueue.push(node);
    return vertex;
  }

  *initializeSteps(
    tables: ReadonlyMap<string, t.ArrayExpression>,
  ): Generator<void> {
    let examined = 0;
    const admitted = new Set<string>();
    const patternWrites = new WeakMap<t.AssignmentExpression, Set<string>>();
    for (const [owner, table] of tables) {
      if (examined++ % 1024 === 0) yield;
      admitted.add(owner);
      const helper: ViteCacheAllocation = { kind: "helper", owner };
      const cache = this.vertex({});
      cache.seed = { allocation: { kind: "cache", owner, node: table }, owner };
      this.allocations.set(owner, cache);
      const tableVertex = this.normalize(table);
      this.connect(cache, { kind: "family", source: tableVertex });
      const initialization = this.state.parentsByNode.get(table);
      if (initialization !== undefined)
        this.cacheInitializations.add(initialization);
      this.allocationVertices.set(cache.seed.allocation!, cache);
      const helperVertex = this.vertex(owner);
      helperVertex.seed = { allocation: helper, owner };
      this.allocationVertices.set(helper, helperVertex);
      this.connect(helperVertex, { kind: "family", source: cache });
    }
    for (const binding of this.state.bindingsById.values()) {
      if (examined++ % 1024 === 0) yield;
      if (admitted.has(binding.bindingId)) continue;
      const target = this.vertex(binding.bindingId);
      const groups: readonly (readonly JavaScriptSemanticBindingState["referenceInitializers"][number][])[] =
        [binding.initializers, binding.referenceInitializers];
      for (const initializers of groups)
        for (const initializer of initializers) {
          if (examined++ % 1024 === 0) yield;
          const expression = initializer.node;
          if (
            t.isAssignmentExpression(expression, { operator: "=" }) &&
            (t.isObjectPattern(expression.left) ||
              t.isArrayPattern(expression.left)) &&
            initializer.projection.length === 0
          ) {
            let written = patternWrites.get(expression);
            if (written === undefined) {
              written = new Set();
              patternWrites.set(expression, written);
              const destinations = written;
              yield* semanticWriteTargetsSteps(expression.left, (target) => {
                if (t.isIdentifier(target)) {
                  const selected = resolveSemanticBindingState(
                    this.state,
                    target,
                    target.name,
                  );
                  if (selected !== undefined)
                    destinations.add(selected.bindingId);
                }
                return false;
              });
            }
            // An opaque pattern initializer denotes an unknown selected leaf,
            // not the RHS wrapper allocation. Retain its possible cache family.
            if (written.has(binding.bindingId)) {
              target.seed = UNKNOWN;
              this.connect(target, {
                kind: "family",
                source: this.normalize(expression.right),
              });
              continue;
            }
          }
          const source = this.project(
            this.normalize(initializer.node),
            initializer.projection,
            initializer.node,
          );
          if (initializer.copyKind === undefined)
            this.connect(target, { kind: "alias", source });
          else {
            const offset =
              initializer.copyProjectionOffset ?? initializer.projection.length;
            const beforeCopy = this.project(
              this.normalize(initializer.node),
              initializer.projection.slice(0, offset),
              initializer.node,
            );
            const copy = this.vertex({});
            copy.seed = {
              allocation: {
                kind: "container",
                node: initializer.node,
                copy: { source: beforeCopy, initializer },
              },
              owner: undefined,
            };
            this.allocationVertices.set(copy.seed.allocation!, copy);
            this.connect(copy, { kind: "copy-family", source: beforeCopy });
            this.connect(target, {
              kind: "alias",
              source: this.project(
                copy,
                initializer.projection.slice(offset + 1),
                initializer.node,
              ),
            });
          }
        }
      if (target.inputs.length === 0) target.seed = UNKNOWN;
    }
  }

  /** index local slot effects before the snapshot pass; effects remain source facts. */
  *retainSnapshotsSteps(
    writes: readonly ViteCacheWrite[],
    escapes: readonly { readonly node: t.Node; readonly value: t.Node }[],
  ): Generator<void> {
    let examined = 0;
    for (const write of writes) {
      if (examined++ % 1024 === 0) yield;
      // The admitted initializer already defines this cache allocation and its
      // literal slots; it is not a later replacement of the helper's f property.
      if (this.cacheInitializations.has(write.node)) continue;
      const receiver = this.normalize(write.receiver);
      const receivers = this.writeReceivers.get(receiver) ?? [];
      receivers.push(write);
      this.writeReceivers.set(receiver, receivers);
      this.retainWrite(write);
    }
    yield* this.properties.retainRestrictionsSteps();
    for (const escape of escapes) {
      if (examined++ % 1024 === 0) yield;
      const allocation = this.read(escape.value)?.allocation;
      if (allocation?.kind !== "container") continue;
      const retained = this.properties.escapes.get(allocation) ?? [];
      retained.push(escape.node);
      this.properties.escapes.set(allocation, retained);
    }
    this.snapshots = true;
    this.reads.clear();
    for (const vertex of this.vertices.values()) {
      if (examined++ % 1024 === 0) yield;
      delete vertex.fact;
      this.enqueue(vertex);
    }
    for (const [allocation, retained] of this.properties.writes) {
      const target = this.allocationVertices.get(allocation);
      if (target === undefined) continue;
      for (const write of retained) {
        if (examined++ % 1024 === 0) yield;
        if (write.value !== undefined)
          this.connect(target, {
            kind: "family",
            source: this.normalize(write.value),
          });
      }
    }
  }

  private retainWrite(write: ViteCacheWrite): void {
    const allocation = this.read(write.receiver)?.allocation;
    if (
      allocation?.kind !== "container" &&
      allocation?.kind !== "cache" &&
      allocation?.kind !== "helper"
    )
      return;
    const retained = this.properties.writes.get(allocation) ?? [];
    retained.push(write);
    this.retainedWrites.set(write, allocation);
    this.properties.writes.set(allocation, retained);
    if (write.value !== undefined) this.normalize(write.value);
  }

  *solveSteps(): Generator<void> {
    let examined = 0;
    let defaultsCursor = 0;
    const unresolvedDefaults = new Set<DefaultInput>();
    for (const vertex of this.vertices.values()) {
      if (examined++ % 1024 === 0) yield;
      this.enqueue(vertex);
    }
    let cursor = 0;
    for (;;) {
      while (this.normalizeQueue.length > 0 || cursor < this.pending.length) {
        yield* this.normalizeSteps();
        const vertex = this.pending[cursor++];
        if (vertex === undefined) continue;
        this.queued.delete(vertex);
        if (cursor % 1024 === 0) yield;
        let incoming = vertex.seed;
        for (const input of vertex.inputs) {
          if (examined++ % 1024 === 0) yield;
          const value = yield* this.inputValueSteps(
            input,
            vertex,
            unresolvedDefaults,
          );
          if (value !== undefined) incoming = joinIdentity(incoming, value);
        }
        if (incoming === undefined) continue;
        const next = joinIdentity(vertex.fact, incoming);
        if (next === vertex.fact) continue;
        vertex.fact = next;
        if (next.allocation?.kind === "cache" && next.owner === null)
          this.ambiguousCacheFamily = true;
        if (this.snapshots)
          for (const write of this.writeReceivers.get(vertex) ?? []) {
            if (examined++ % 1024 === 0) yield;
            if (
              this.retainedWrites.get(write) === next.allocation ||
              (next.allocation?.kind !== "container" &&
                next.allocation?.kind !== "cache" &&
                next.allocation?.kind !== "helper")
            )
              continue;
            this.retainedWrites.set(write, next.allocation);
            this.properties.retainLateWrite(next.allocation, write);
            const container = this.allocationVertices.get(next.allocation);
            if (container !== undefined && write.value !== undefined)
              this.connect(container, {
                kind: "family",
                source: this.normalize(write.value),
              });
          }
        for (const listener of vertex.listeners) {
          if (examined++ % 1024 === 0) yield;
          this.enqueue(listener);
        }
      }
      // A bottom alias cycle is still an unproven argument, not proof that its
      // default is absent. Widen only after ready arguments reached a fixed point.
      while (defaultsCursor < this.defaultChoices.length) {
        if (examined++ % 1024 === 0) yield;
        const choice = this.defaultChoices[defaultsCursor++];
        if (choice !== undefined && choice.input.source.fact === undefined) {
          unresolvedDefaults.add(choice.input);
          this.enqueue(choice.target);
        }
      }
      if (cursor === this.pending.length && this.normalizeQueue.length === 0)
        break;
    }
    this.pending.length = 0;
    this.queued.clear();
  }

  private vertex(key: VertexKey): Vertex {
    let vertex = this.vertices.get(key);
    if (vertex === undefined) {
      vertex = { key, inputs: [], listeners: new Set() };
      this.vertices.set(key, vertex);
    }
    return vertex;
  }

  private *inputValueSteps(
    input: Input,
    vertex: Vertex,
    unresolvedDefaults: ReadonlySet<DefaultInput>,
  ): Generator<void, ViteCacheIdentity | undefined> {
    const source =
      input.source.fact ??
      (input.kind === "default" && unresolvedDefaults.has(input)
        ? UNKNOWN
        : undefined);
    if (source === undefined) return undefined;
    if (input.kind === "default")
      return providedDefaultInput(input, source)
        ? source
        : input.fallback.fact === undefined
          ? undefined
          : joinIdentity(source, input.fallback.fact);
    if (input.kind === "helper-result")
      return yield* this.helperResultSteps(source, input, vertex);
    if (input.kind === "select")
      return yield* this.selectSteps(source, input, vertex);
    if (input.kind === "alias") return source;
    const owner =
      input.kind === "copy-family" && source.allocation?.kind === "cache"
        ? source.children
        : source.owner;
    return {
      allocation: vertex.seed?.allocation ?? null,
      owner,
      children: owner,
    };
  }

  private *helperResultSteps(
    source: ViteCacheIdentity,
    input: Extract<Input, { kind: "helper-result" }>,
    target: Vertex,
  ): Generator<void, ViteCacheIdentity | undefined> {
    if (source.allocation?.kind !== "helper")
      return { allocation: null, owner: source.owner };
    const owner = source.allocation.owner ?? "";
    const cache = this.allocations.get(owner);
    if (cache === undefined) return UNKNOWN;
    let result = this.helperResults.get(input.call);
    if (result === undefined) {
      result = this.vertex({});
      this.helperResults.set(input.call, result);
      const indexes = input.call.arguments[0];
      const selection =
        indexes === undefined
          ? undefined
          : unwrapJavaScriptExpression(indexes).node;
      const table = yield* this.helperTableSteps(
        input.call,
        cache,
        owner,
        t.isArrayExpression(selection),
      );
      const keys: (string | null | undefined)[] = [];
      let unknownFrom: number | undefined = t.isArrayExpression(selection)
        ? undefined
        : 0;
      let uncertain = !t.isArrayExpression(selection);
      if (t.isArrayExpression(selection)) {
        let examined = 0;
        for (const index of selection.elements) {
          if (examined++ % 1024 === 0) yield;
          if (t.isSpreadElement(index)) {
            unknownFrom = keys.length;
            uncertain = true;
            break;
          }
          const key =
            index === null ? undefined : semanticStaticPropertyKey(index, true);
          keys.push(key);
          if (key === undefined) continue;
          if (key === null) uncertain = true;
          else
            this.connect(result, {
              kind: "family",
              source: this.project(table, [key], input.call),
            });
        }
      }
      if (uncertain)
        this.connect(result, { kind: "copy-family", source: table });
      const allocation: ViteCacheAllocation = {
        kind: "container",
        node: input.call,
        helperResult: {
          table,
          keys,
          unknownFrom,
          read: input.call,
          family: result,
        },
      };
      result.seed = { allocation, owner: undefined };
      this.allocationVertices.set(allocation, result);
      this.enqueue(result);
    }
    result.listeners.add(target);
    return result.fact;
  }

  private *helperTableSteps(
    call: t.CallExpression | t.OptionalCallExpression,
    cache: Vertex,
    owner: string,
    freshIndexes: boolean,
  ): Generator<void, Vertex> {
    const arguments_ = call.arguments;
    if (
      arguments_.slice(0, 3).some((argument) => t.isSpreadElement(argument))
    ) {
      const table = this.vertex({});
      table.seed = UNKNOWN;
      this.connect(table, { kind: "copy-family", source: cache });
      let examined = 0;
      for (const argument of arguments_) {
        if (examined++ % 1024 === 0) yield;
        this.connect(table, {
          kind: "family",
          source: this.normalize(
            t.isSpreadElement(argument) ? argument.argument : argument,
          ),
        });
      }
      return table;
    }
    const usesDefault = (node: t.Node | undefined): boolean =>
      node === undefined || isJavaScriptViteDefaultUndefined(node, this.state);
    const mapperArgument = arguments_[1];
    let fallback = cache;
    let mapperTable: Vertex | undefined;
    if (mapperArgument !== undefined && !usesDefault(mapperArgument)) {
      const mapper = this.defaultChoice(
        this.normalize(mapperArgument),
        this.vertex(owner),
        mapperArgument,
      ).vertex;
      const contextual = this.vertex({});
      contextual.seed = UNKNOWN;
      this.connect(contextual, { kind: "copy-family", source: cache });
      this.connect(contextual, { kind: "family", source: mapper });
      // A provided mapper can already own a table. Its unproven initializer
      // context retains sharing without pretending its m parameter is default.
      mapperTable = this.project(mapper, ["f"], call);
      fallback = this.defaultChoice(mapperTable, contextual).vertex;
    }
    const tableArgument = arguments_[2];
    const provided =
      tableArgument === undefined || usesDefault(tableArgument)
        ? undefined
        : this.defaultChoice(
            this.normalize(tableArgument),
            fallback,
            tableArgument,
          );
    this.helperArgumentReads.set(call, {
      freshIndexes,
      table: provided === undefined ? undefined : tableArgument,
      mapper: mapperArgument,
      providedTable: provided?.input,
      mapperTable,
    });
    return provided?.vertex ?? fallback;
  }

  private defaultChoice(
    source: Vertex,
    fallback: Vertex,
    node?: t.Node,
  ): { vertex: Vertex; input: DefaultInput } {
    const selected = this.vertex({});
    const input: DefaultInput = {
      kind: "default",
      source,
      fallback,
      defined:
        node !== undefined &&
        (t.isLiteral(node) ||
          t.isArrayExpression(node) ||
          t.isObjectExpression(node) ||
          t.isFunction(node) ||
          t.isClass(node)),
    };
    this.connect(selected, input);
    return { vertex: selected, input };
  }

  private enqueue(vertex: Vertex): void {
    if (this.queued.has(vertex)) return;
    this.queued.add(vertex);
    this.pending.push(vertex);
  }

  private connect(target: Vertex, input: Input): void {
    target.inputs.push(input);
    input.source.listeners.add(target);
    if (input.kind === "default") {
      input.fallback.listeners.add(target);
      this.defaultChoices.push({ target, input });
    }
    this.enqueue(target);
  }

  private project(
    source: Vertex,
    path: readonly (string | number | null)[],
    read: t.Node,
  ): Vertex {
    let current = source;
    for (const segment of path) {
      const key = segment === null ? null : String(segment);
      const byKey =
        this.reads.get(current) ?? new Map<Key, Map<t.Node, Vertex>>();
      this.reads.set(current, byKey);
      const byRead = byKey.get(key) ?? new Map<t.Node, Vertex>();
      byKey.set(key, byRead);
      let selected = byRead.get(read);
      if (selected === undefined) {
        selected = this.vertex({});
        byRead.set(read, selected);
        this.connect(selected, { kind: "select", source: current, key, read });
      }
      current = selected;
    }
    return current;
  }

  private *normalizeSteps(): Generator<void> {
    let examined = 0;
    while (this.normalizeQueue.length > 0) {
      if (examined++ % 1024 === 0) yield;
      const node = this.normalizeQueue.pop();
      if (node === undefined) break;
      const vertex = this.vertex(node);
      const expression = unwrapJavaScriptExpression(node).node;
      if (expression !== node) {
        this.connect(vertex, {
          kind: "alias",
          source: this.normalize(expression),
        });
        continue;
      }
      const invocation =
        t.isCallExpression(expression) || t.isOptionalCallExpression(expression)
          ? this.invocation(expression)
          : undefined;
      if (
        invocation?.kind === "known" &&
        invocation.path.length === 3 &&
        invocation.path[0] === "intrinsic" &&
        invocation.path[1] === "Object" &&
        OBJECT_TARGET_RESULTS.has(invocation.path[2] ?? "")
      ) {
        const target = invocation.arguments?.[0];
        if (target === undefined || t.isSpreadElement(target))
          vertex.seed = UNKNOWN;
        else
          this.connect(vertex, {
            kind: "alias",
            source: this.normalize(target),
          });
        continue;
      }
      if (
        t.isObjectExpression(expression) ||
        t.isArrayExpression(expression) ||
        viteCacheObjectOperation(expression, this.invocation) !== undefined
      ) {
        yield* this.normalizeContainerSteps(vertex, expression);
        continue;
      }
      if (
        t.isCallExpression(expression) ||
        t.isOptionalCallExpression(expression)
      ) {
        this.connect(vertex, {
          kind: "helper-result",
          source: this.normalize(expression.callee),
          call: expression,
        });
        continue;
      }
      if (t.isIdentifier(expression)) {
        const binding = resolveSemanticBindingState(
          this.state,
          expression,
          expression.name,
        );
        if (binding === undefined) vertex.seed = UNKNOWN;
        else
          this.connect(vertex, {
            kind: "alias",
            source: this.vertex(binding.bindingId),
          });
      } else if (
        t.isMemberExpression(expression) ||
        t.isOptionalMemberExpression(expression)
      ) {
        this.connect(vertex, {
          kind: "select",
          source: this.normalize(expression.object),
          key: semanticStaticPropertyKey(
            expression.property,
            expression.computed,
          ),
          read: expression,
        });
      } else if (
        t.isConditionalExpression(expression) ||
        t.isLogicalExpression(expression)
      ) {
        for (const child of t.isConditionalExpression(expression)
          ? [expression.consequent, expression.alternate]
          : [expression.left, expression.right])
          this.connect(vertex, {
            kind: "alias",
            source: this.normalize(child),
          });
      } else if (
        t.isSequenceExpression(expression) ||
        t.isAssignmentExpression(expression, { operator: "=" })
      ) {
        const value = t.isSequenceExpression(expression)
          ? expression.expressions.at(-1)
          : expression.right;
        if (value !== undefined)
          this.connect(vertex, {
            kind: "alias",
            source: this.normalize(value),
          });
      } else vertex.seed = foreignAllocation(expression) ? FOREIGN : UNKNOWN;
      this.enqueue(vertex);
    }
  }

  private *normalizeContainerSteps(
    vertex: Vertex,
    expression: t.Node,
  ): Generator<void> {
    const allocation: ViteCacheAllocation = {
      kind: "container",
      node: expression,
    };
    vertex.seed = { allocation, owner: undefined };
    this.allocationVertices.set(allocation, vertex);
    const children = t.isObjectExpression(expression)
      ? expression.properties
      : t.isArrayExpression(expression)
        ? expression.elements
        : t.isCallExpression(expression)
          ? (this.invocation(expression)?.arguments ?? [])
          : [];
    let examined = 0;
    for (const child of children) {
      if (examined++ % 1024 === 0) yield;
      if (child === null) continue;
      const value = t.isSpreadElement(child)
        ? child.argument
        : t.isObjectProperty(child)
          ? child.value
          : child;
      this.connect(vertex, {
        kind:
          t.isSpreadElement(child) || t.isCallExpression(expression)
            ? "copy-family"
            : "family",
        source: this.normalize(value),
      });
    }
    this.enqueue(vertex);
  }

  private *selectSteps(
    source: ViteCacheIdentity,
    input: Extract<Input, { kind: "select" }>,
    target: Vertex,
  ): Generator<void, ViteCacheIdentity | undefined> {
    const allocation = source.allocation;
    if (allocation === null) return { allocation: null, owner: source.owner };
    if (allocation.kind === "helper") {
      const cache = this.allocations.get(allocation.owner ?? "");
      if (input.key === "f" && cache !== undefined) {
        const selected = this.snapshots
          ? yield* this.properties.snapshotSteps(
              cache,
              allocation,
              "f",
              input.read,
            )
          : cache;
        selected.listeners.add(target);
        return selected.fact;
      }
    }
    if (
      allocation.kind !== "container" &&
      allocation.kind !== "cache" &&
      allocation.kind !== "helper"
    )
      return FOREIGN;
    if (input.key === null) return { allocation: null, owner: source.owner };
    const slot = yield* this.properties.slotSteps(allocation, input.key);
    const selected = this.snapshots
      ? yield* this.properties.snapshotSteps(
          slot,
          allocation,
          input.key,
          input.read,
        )
      : slot;
    if (!selected.listeners.has(target)) selected.listeners.add(target);
    const fact = selected.fact;
    if (fact === undefined) return undefined;
    return fact.allocation === null && fact.owner === undefined
      ? { allocation: null, owner: source.owner }
      : fact;
  }
}

const foreignAllocation = (node: t.Node): boolean =>
  t.isLiteral(node) ||
  t.isFunction(node) ||
  t.isObjectMethod(node) ||
  t.isClass(node);
