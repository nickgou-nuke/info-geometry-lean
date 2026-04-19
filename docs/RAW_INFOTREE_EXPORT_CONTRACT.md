# Raw InfoTree Export Contract

This contract defines the future faithful compiler-memory layer. It is stricter
than the current raw DAG dependency layer.

## Boundary

The `raw_infotree_*` family is the preserved Lean compiler/metaprogramming
`InfoTree` layer. It is not a retrieval graph, not an SCC quotient, and not the
declaration dependency graph.

It is also not a replacement for Lean's compiled artifacts:

- `.olean` is the compiled module-environment artifact. It serializes
  `Environment.ModuleData`: imports, constants, extra constant names, and
  persistent environment-extension entries. It is the right source for
  declaration/environment facts.
- `.ilean` is the reference/location sidecar produced from InfoTree-derived
  reference extraction. It is the right source for editor-style references and
  source locations.
- `raw_infotree_*` is a loss-audited elaboration-topology sidecar. It persists
  the runtime/server layer that Lean exposes through `InfoTree` and snapshots:
  command topology, context fibers, goal/tactic-adjacent metadata, term nodes,
  macro expansion surfaces, and projection leakage.

Therefore `raw_infotree_*` must join to `.olean` and `.ilean`; it must not
pretend to subsume them.

Required collections:

- `raw_infotree_roots`: one root per exported `InfoTree`.
- `raw_infotree_nodes`: every node reached while walking the exported tree.
- `raw_infotree_edges`: every parent-child edge, with sibling order.
- `raw_infotree_contexts`: context/provenance payloads attached to context
  wrappers when exportable.
- `raw_infotree_payloads`: term/tactic/message/widget payloads as emitted by
  Lean, without semantic rewriting.
- `raw_infotree_payload_fields`: constructor-specific payload fields split out
  for indexing; these are redundant with the payload text, not a replacement
  for it.
- `raw_infotree_decl_links`: links from InfoTree nodes to declarations when a
  declaration relation is available.
- `raw_infotree_env_refs`: stable environment references and provenance facts
  for command contexts. These are join surfaces, not full environment
  snapshots. They include stable hashes/counts for direct imports and all
  imported modules.
- `raw_infotree_mctx_refs`: stable metavariable-context references and
  provenance facts for command contexts. These are join surfaces, not full
  metavariable-context serialization. They include stable hashes/counts for
  exposed metavariable declaration ids and user-name mappings.
- `raw_infotree_mctx_decls`: stage-level structural facts for metavariable
  declarations visible in a command context: metavariable id, user name, kind,
  depth/index/scope counters, local-context size, local-instance count, type
  text/hash, and assignment/delayed-assignment presence with exposed
  expression text/hash when available. This is not full local-context or
  expression graph serialization.
- `raw_infotree_projection_leakage`: every omitted field or unavailable payload
  class, with a reason.

Node-adjacent tables (`contexts`, `payloads`, `payload_fields`, `decl_links`,
`env_refs`, `mctx_refs`, and `mctx_decls`) also carry redundant `rootKey`,
`file`, and `module` fields for direct Arango filtering. These fields are query
accelerators, not a second source of truth. The authoritative provenance path
remains:

```text
row.nodeKey -> raw_infotree_nodes.rootKey -> raw_infotree_roots.file/module
```

Validation must reject any denormalized provenance that disagrees with this
join path.

## Invariants

- Unknown compiler state must be represented as `null`/absent plus leakage,
  never as numeric zero. A zero is allowed only when Lean actually reports zero.
- The raw layer is append-only/loss-audited.
- `.olean` remains the compiled-environment authority. `.ilean` remains the
  reference/location sidecar. `raw_infotree_*` records elaboration topology and
  must carry enough file/module/root/node keys to join back to both.
- Every exported root has at least one node or an explicit leakage row.
- Every child relation in the walked tree is emitted exactly once.
- Every edge has `sibling_index`.
- Every node-adjacent row with denormalized `rootKey`/`file`/`module` must
  agree with the normalized node/root provenance path.
- Every overlay points back to raw roots/nodes/edges.
- Absence from `ig_*`, `raw_info_*`, or SCC overlays is never evidence of
  absence from `raw_infotree_*`.
- Unknown compiler state is encoded as `null`/absent plus a leakage row, never
  as numeric zero. A zero is allowed only when Lean exposed a real zero-valued
  measurement, for example an actually empty local context in a `TermInfo`.

## Stage 1 Probe

`lean/DAG/RawInfoTreeExport.lean` is the first probe. It walks
`commandState.infoState.trees` after frontend commands and emits:

- roots
- nodes
- parent-child edges
- payload rows for term/tactic nodes when Lean exposes a stable text surface
- context rows for context wrappers
- environment and metavariable-context reference rows for command contexts
- metavariable declaration rows for command contexts
- declaration links when they are trivial to extract from a constant expression
- leakage rows for holes and payload/context fields not yet captured

This probe establishes topology preservation and begins context/decl-link
materialization before attempting full payload fidelity. It is therefore
**loss-audited**, not yet **fully lossless**.

Current known limitations:

- `InfoTree.context` carries `PartialContextInfo` in Lean 4.28. Stage 1 emits a
  typed context row. `commandCtx` rows include real exposed `mctx_size`,
  `mctx_depth`, namespace, open declarations, file-map source/positions,
  options entries, and name-generator state. `parentDeclCtx` rows include the
  parent declaration name. `autoImplicitCtx` rows include the exposed
  auto-implicit expressions.
  Stage 1 also emits `raw_infotree_env_refs` and `raw_infotree_mctx_refs` rows
  with stable hash/count identity and provenance facts. These rows make
  downstream joins non-fake, but they are not full serializers. Full
  environment snapshots, final command environments, and full
  metavariable-context structures remain leakage until they have separate
  structural serializers.
  `raw_infotree_mctx_decls` reduces this gap by exporting stable declaration
  facts for each exposed metavariable declaration, including assignment
  presence and exposed assignment text/hash. It still does not serialize the
  full local context as rows, nor does it serialize expressions as a lossless
  expression graph, so `command_context_mctx` remains leakage.
  The context row must not contain placeholder `0` values for unresolved state;
  stale probe artifacts with untyped `lctx_size = 0` / `mctx_size = 0` are
  invalid and must be regenerated. A typed `commandCtx` may legitimately have
  `mctx_size = 0` when Lean exposed an empty metavariable context.
- `TermInfo` and `DelabTermInfo` emit expression/expected-type/syntax payloads
  and declaration links for constants found in their expressions.
- `CommandInfo`, `MacroExpansionInfo`, `OptionInfo`, `ErrorNameInfo`,
  `FieldInfo`, `FVarAliasInfo`, `FieldRedeclInfo`, `DocInfo`, and
  `DocElabInfo` have constructor-specific payload surfaces.
- `FieldInfo` links to `projName` and constants found in `val`; no nonexistent
  Lean 4.28 owner field is assumed.
- `TacticInfo` emits tactic syntax and before/after goal counts. Full
  metavariable-context serialization remains leakage.
- `CompletionInfo` emits constructor-specific payload surfaces for `dot`,
  `id`, `dotId`, `fieldId`, `namespaceId`, `option`, `errorName`,
  `endSection`, and `tactic` completions.
- Custom dynamic payloads, widget internals, and some failed-choice internals
  remain topology-preserved with leakage rows until constructor-specific
  serializers are added.

## Promotion Rule

Only after the leakage rows are reduced to represent Lean-internal
non-exportability may the Arango layer be called faithful to the compiler
`InfoTree`. Until then, the current faithful layer remains:

```text
lossless raw DAG dependency export + topology-preserving overlays
```

Validation must distinguish topology validity from losslessness. A stage probe
may pass topology validation while still reporting `lossless_ok = false`.
Promotion to the raw compiler-memory layer requires:

```text
metadata.fully_lossless == true
raw_infotree_projection_leakage row count == 0
```
