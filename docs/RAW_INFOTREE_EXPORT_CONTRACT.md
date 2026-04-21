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
  Hole nodes must carry the exact `MVarId`; assignment/lazy-assignment closure
  is tracked separately as leakage until `InfoState.assignment` and
  `InfoState.lazyAssignment` are serialized.
- `raw_infotree_edges`: every parent-child edge, with sibling order.
- `raw_infotree_contexts`: context/provenance payloads attached to context
  wrappers when exportable.
- `raw_infotree_payloads`: term/tactic/message/widget payloads as emitted by
  Lean, without semantic rewriting.
- `raw_infotree_payload_fields`: constructor-specific payload fields split out
  for indexing. Payload text is only a compact convenience projection; the
  split fields are the query surface.
- `raw_infotree_decl_links`: links from InfoTree nodes to declarations when a
  declaration relation is available.
- `raw_infotree_env_refs`: stable environment references and provenance facts
  for command contexts. These are join surfaces, not full environment
  snapshots. They intentionally keep only compact exposed counts/presence;
  full import lists and environments remain leakage until a structural
  environment table exists.
- `raw_infotree_mctx_refs`: stable metavariable-context occurrence references and
  provenance facts for command contexts. These are join surfaces, not full
  metavariable-context serialization. They include stable hashes/counts for
  exposed metavariable declaration ids and user-name mappings, plus an interned
  `mctxKey`. Stage 2 also emits refs for `TacticInfo.mctxBefore` and
  `TacticInfo.mctxAfter`.
- `raw_infotree_mctx_decls`: stage-level structural facts for metavariable
  declarations visible through an interned `mctxKey`: metavariable id, user
  name, kind, depth/index/scope counters, local-context size, local-instance
  count, type hash projection, and assignment/delayed-assignment presence with
  exposed expression hash projection when available. This is not full
  local-context or expression graph serialization.
- `raw_infotree_lctx_refs`: local-context occurrence references. These preserve
  every descent occurrence from term/field/macro/completion/delab/mctx surfaces
  to an interned `lctxKey`.
- `raw_infotree_lctx_decls`: stage-level structural facts for local
  declarations visible in `LocalContext` surfaces: free-variable id, user name,
  local-declaration kind, index, binder info for `cdecl`, let/nondep/value
  fields for `ldecl`, aux full name when exposed, and type/value hash
  projections. Rows are keyed by interned `lctxKey`; occurrence multiplicity is
  preserved by `raw_infotree_lctx_refs`.
- `raw_infotree_projection_leakage`: every omitted field or unavailable payload
  class, with a reason.

Node-adjacent tables (`contexts`, `payloads`, `payload_fields`, `decl_links`,
`env_refs`, `mctx_refs`, `mctx_decls`, `lctx_refs`, and `lctx_decls`) also carry redundant
`rootKey`, `file`, and `module` fields for direct Arango filtering. These
fields are query accelerators, not a second source of truth. The authoritative
provenance path remains:

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

## Stage 2 Tactic/Lctx Bridge

`lean/DAG/RawInfoTreeExport.lean` follows the LeanDojo extraction pattern: it
uses `IO.processCommands`, then walks the final
`commandState.infoState.trees.toArray`. This is required for tactic InfoTree
surfaces; incremental frontend hooks can miss the finalized tactic-state
forest. The exporter emits:

- roots
- nodes
- parent-child edges
- payload rows for term/tactic nodes when Lean exposes a stable text surface
- context rows for context wrappers
- environment and metavariable-context reference rows for command contexts
- metavariable declaration rows for command contexts
- tactic before/after metavariable-context refs and declaration rows
- local-context declaration rows for term/macro/field/completion/delab/mctx
  declaration local contexts
- declaration links when they are trivial to extract from a constant expression
- leakage rows for holes and payload/context fields not yet captured

This probe establishes topology preservation, context/decl-link
materialization, command and tactic metavariable-context
reference/declaration bridges, and the first structural local-context
declaration bridge before attempting full payload fidelity. It is therefore
**loss-audited**, not yet **fully lossless**.

Current known limitations:

- `InfoTree.context` carries `PartialContextInfo` in Lean 4.28. Stage 1 emits a
  typed context row. `commandCtx` rows include real exposed `mctx_size`,
  `mctx_depth`, namespace, open-declaration count, file-position count,
  options count, and name-generator state. `parentDeclCtx` rows include the
  parent declaration name. `autoImplicitCtx` rows include the exposed
  auto-implicit expression hash projections. Full file-map source text, open
  declarations, options, and auto-implicit expressions remain leakage where
  they are not structured rows.
  Stage 1 also emits `raw_infotree_env_refs` and `raw_infotree_mctx_refs` rows
  with stable hash/count identity and provenance facts. These rows make
  downstream joins non-fake, but they are not full serializers. Full
  environment snapshots, final command environments, and full
  metavariable-context structures remain leakage until they have separate
  structural serializers.
  `raw_infotree_mctx_decls` reduces this gap by exporting stable declaration
  facts for each exposed metavariable declaration, including assignment
  presence and exposed assignment hash projections. It still does not serialize the
  full expression graph for types/assignments, so `command_context_mctx`
  remains leakage.
  `raw_infotree_lctx_decls` exports the first structural local-context bridge:
  local declaration ids, names, kinds, indices, binder/let/nondep/value
  surfaces, aux full names, and type/value hash projections for exposed lctx
  surfaces. This reclaims binder/local-variable topology, but the type/value
  expressions inside each local declaration are still text/hash projections,
  not lossless expression graphs.
  The context row must not contain placeholder `0` values for unresolved state;
  stale probe artifacts with untyped `lctx_size = 0` / `mctx_size = 0` are
  invalid and must be regenerated. A typed `commandCtx` may legitimately have
  `mctx_size = 0` when Lean exposed an empty metavariable context.
- `TermInfo` and `DelabTermInfo` emit expression/expected-type/syntax hash
  projections. Declaration links are emitted only where Lean exposes stable
  names directly; full expression constant traversal belongs to the future Expr
  DAG table. These are
  useful projections, not lossless expression/syntax/local-context
  serialization; the exporter now records explicit leakage rows for missing
  `Expr` and `Syntax` graphs while `raw_infotree_lctx_decls` carries the
  exposed local declarations. `DelabTermInfo` additionally
  emits its `location?`, `docString?`, and `explicit` surfaces, while recording
  that `DeclarationLocation` is still not a structured table.
- `CommandInfo`, `MacroExpansionInfo`, `OptionInfo`, `ErrorNameInfo`,
  `FieldInfo`, `FVarAliasInfo`, `FieldRedeclInfo`, `DocInfo`, and
  `DocElabInfo` have constructor-specific payload surfaces.
- `FieldInfo` links to `projName` and constants found in `val`; no nonexistent
  Lean 4.28 owner field is assumed.
- `TacticInfo` emits tactic syntax, before/after goal counts, exact
  before/after goal `MVarId`s, and separate `raw_infotree_mctx_refs`,
  `raw_infotree_mctx_decls`, and `raw_infotree_lctx_decls` rows for
  `mctxBefore` and `mctxAfter`. Full expression graph and assignment-closure
  fidelity remain leakage.
- `CompletionInfo` emits constructor-specific payload surfaces for `dot`,
  `id`, `dotId`, `fieldId`, `namespaceId`, `option`, `errorName`,
  `endSection`, and `tactic` completions.
- Custom dynamic payloads, widget internals, and some failed-choice internals
  remain topology-preserved with leakage rows until constructor-specific
  serializers are added.
- Hole nodes preserve their `MVarId`. Resolved/lazy hole assignment maps from
  `InfoState` remain leakage, because the current export walks reported trees
  and does not serialize `InfoState.assignment` or `InfoState.lazyAssignment` as
  separate rows.

## Stage 2 Leakage Checklist

Easy targets already captured or ready to capture without full graph
serialization:

- `parentDeclCtx.parentDecl`: captured as `parentDecl`.
- `InfoTree.hole.mvarId`: captured as `holeMVarId`.
- `TacticInfo.goalsBefore` / `goalsAfter`: captured as exact goal IDs plus
  counts.
- `DelabTermInfo.location?`, `docString?`, `explicit`: captured as stage-level
  fields; location still needs a structured declaration-location table.
- Declaration names from term/field/option/error/doc surfaces: captured as
  `raw_infotree_decl_links` where Lean exposes stable names.
- `CommandContextInfo.fileMap` and `ngen`: captured structurally from their
  Lean 4.28 fields.

Hard proxy labels that must stay visible to Arango/agents:

- `command_context_env`: full `Environment`, beyond import/name hashes.
- `command_context_cmd_env`: final command `Environment`, when present.
- `command_context_mctx`: full `MetavarContext`, beyond refs and declaration
  rows.
- `term_expr_graph`, `term_expected_type_expr_graph`, `term_lctx`: full
  `TermInfo` expression fibers and the residual LocalContext object graph not
  captured by `raw_infotree_lctx_decls`.
- `tactic_mctx_before`, `tactic_mctx_after`: residual expression graph and
  assignment-closure debt for tactic-local before/after metavariable contexts;
  refs, declaration rows, and local-context rows are now exported.
- `macro_expansion_input_syntax_object` /
  `macro_expansion_output_syntax_object`: full `Syntax` object fidelity.
- `field_value_expr_graph` and `field_lctx`: field expression fibers and the
  residual LocalContext object graph not captured by `raw_infotree_lctx_decls`.
- `hole_assignment`: `InfoState.assignment` / `lazyAssignment` closure.
- `custom_dynamic_value` and `user_widget_payload`: payloads that require
  type-specific serializers.

The mctx bridge currently reclaims command-context facts: context depth,
counters, declaration IDs, user-name mappings, metavariable declaration kind,
local-context size, local-instance count, type text/hash, assignment
presence/text/hash, delayed-assignment markers, and local declarations inside
each exposed metavariable declaration context. It does not reclaim:

- expression graphs for types and assignments;
- tactic-specific expression graphs and assignment closure inside
  `mctxBefore` / `mctxAfter`;
- full environment snapshots.

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

## Arango Ingest

`tools/infra/arango_raw_infotree_ingest.py` imports this compiler-memory layer
into Arango. It is separate from `arango_layered_ingest.py`, which imports the
lossless raw DAG dependency layer and topology overlay.

For real-codebase export, do not drive the single-file exporter over one large
theorem corridor as the first ingest target. Use the batch wrapper:

```bash
python3 tools/infra/batch_raw_infotree_export.py \
  lean/DAG/SCC.lean lean/DAG/SearchCoreTests.lean \
  --output-dir artifacts/infotree/raw-infotree-batch-real-smoke \
  --timeout-sec 90
```

The batch wrapper follows the LeanDojo discipline:

- require a corresponding built `.olean` for real repo files;
- run `RawInfoTreeExport.lean` per file;
- impose a timeout per file;
- validate every per-file export;
- merge only validated exports;
- leave failed or timed-out files in `batch_report.json`.

Synthetic probes may opt out of the `.olean` gate explicitly:

```bash
python3 tools/infra/batch_raw_infotree_export.py \
  tmp/raw_infotree_stage2_synthetic.lean \
  --allow-missing-olean \
  --output-dir artifacts/infotree/raw-infotree-batch-synthetic
```

The importer first runs `validate_raw_infotree_export.py` unless
`--skip-validation` is explicitly passed. Normal validation is allowed to pass
while leakage remains. `--require-lossless` forwards the strict validator mode
and therefore fails closed until `fully_lossless=true` and leakage is zero.

For large merged batches, the preferred operational split is:

- validate each per-file export before merge;
- stream the already validated merged rows into a clean Arango target with
  `--drop-existing --skip-validation`;
- run `verify_raw_infotree_arango_descent.py` as the topology authority.

This avoids revalidating million-row joins in Python memory. Python preflight is
for schema/count sanity; Arango-side AQL validation is for referential closure,
cross-collection descent, and tactic before/after mctx reachability.

Document collections:

- `raw_infotree_roots`
- `raw_infotree_nodes`
- `raw_infotree_contexts`
- `raw_infotree_payloads`
- `raw_infotree_payload_fields`
- `raw_infotree_decl_links`
- `raw_infotree_env_refs`
- `raw_infotree_mctx_refs`
- `raw_infotree_mctx_decls`
- `raw_infotree_lctx_refs`
- `raw_infotree_lctx_decls`
- `raw_infotree_projection_leakage`

Navigation edge collections:

- `raw_infotree_tree_edges`: parent-child InfoTree topology.
- `raw_infotree_root_node_edges`: root to emitted nodes.
- `raw_infotree_node_context_edges`: node to context row.
- `raw_infotree_node_payload_edges`: node to payload row.
- `raw_infotree_payload_field_edges`: payload to split fields.
- `raw_infotree_node_decl_link_edges`: node to declaration-link rows.
- `raw_infotree_node_env_ref_edges`: node to environment reference rows.
- `raw_infotree_node_mctx_ref_edges`: node to mctx reference rows.
- `raw_infotree_mctx_decl_edges`: mctx reference to interned mctx declarations.
- `raw_infotree_source_lctx_ref_edges`: mctx declaration or node surface to
  local-context occurrence references.
- `raw_infotree_lctx_ref_decl_edges`: local-context occurrence reference to
  interned local declarations.
- `raw_infotree_node_leakage_edges`: node to explicit projection leakage.

Dry-run example:

```bash
python3 tools/infra/arango_raw_infotree_ingest.py \
  --input-dir artifacts/infotree/raw-infotree-probe \
  --dry-run \
  --json-out artifacts/infotree/raw-infotree-probe/arango_ingest_dry_run.json
```

Controlled DB ingest:

```bash
python3 tools/infra/arango_raw_infotree_ingest.py \
  --input-dir artifacts/infotree/raw-infotree-probe \
  --drop-existing \
  --skip-validation \
  --progress-every 500000 \
  --json-out artifacts/infotree/raw-infotree-probe/arango_ingest_report.json
```

Post-ingest descent verification:

```bash
python3 tools/infra/verify_raw_infotree_arango_descent.py \
  --ingest-report artifacts/infotree/raw-infotree-probe/arango_ingest_report.json \
  --json-out artifacts/infotree/raw-infotree-probe/arango_descent_report.json
```

The verifier is non-mutating. It checks that the imported document rows and
navigation edges are referentially closed, that mctx-backed lctx rows descend
from real mctx declarations, that leakage rows remain attached to their source
nodes, and that tactic payloads retain both `tacticBefore` and `tacticAfter`
mctx references. It reports leakage categories by field; it does not reinterpret
leakage as harmless or severe. That policy layer must remain explicit. If the
database contains a partial or stale `raw_infotree_*` import, the verifier
reports the missing collections and exits nonzero rather than running
incomplete descent checks.
