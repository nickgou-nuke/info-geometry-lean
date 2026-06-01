# Arango Faithful InfoTree Target

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

The current Arango lane is useful, but it is not faithful enough to serve as
the full memory of the Lean compiler. `ig_nodes` and `ig_edges` are a retrieval
projection over LeanTrail/DAG artifacts. Expression exports are also projections:
they expose declaration/type/value topology, but they are not the original
compiler `InfoTree`.

The target invariant is stricter:

> Preserve the original Lean compiler/metaprogramming `InfoTree` losslessly
> first; layer hydration, aliases, derived topology, and retrieval projections
> afterward.

Absence from any projection must never be treated as absence from Lean.

## Lean Artifact Boundary

The faithful graph must reuse Lean's artifact split instead of flattening it:

- `.olean` / `.olean.server` / `.olean.private`: compiled module environment.
  These are produced by `Lean.writeModule` from `Environment.ModuleData` and
  remain the authority for imports, constants, persistent environment-extension
  entries, and compiled declaration facts.
- `.ilean`: reference/location sidecar. Lean produces it from InfoTree-derived
  reference extraction, but it is not the full InfoTree.
- `raw_infotree_*`: loss-audited elaboration-topology sidecar. This is the
  persistent Arango-ready image of the runtime/server `InfoTree` layer, not a
  substitute for `.olean` or `.ilean`.

Arango should store joinable views over all three surfaces. It must not treat
`raw_infotree_*` as a replacement for compiled module truth, and it must not
treat `.olean` as if it contains full goal/local-context/metavariable
elaboration topology.

## Permissible Topology Tools

SCC and hydration tools are allowed when used non-destructively. The repo already
has the right primitives:

- `lean/DAG/SCC.lean`: `DAG.tarjan`
- `lean/DAG/Hydrate.lean`: `DAG.hydrate`
- `lean/DAG/Topo.lean`: `DAG.topo`
- `lean/DAG/Dominators.lean`: `DAG.dominators`

These tools do not have to destroy topology. In the Lean API, `HydratedGraph`
extends the original graph and keeps `toGraph` alongside the derived fields:

- `sccs`
- `sccOf`
- `dag`
- `preds`
- `topo`
- `doms`

The lawful use is:

```text
raw graph remains stored losslessly
SCC / hydration / dominators are additive labels and derived views
search uses labels, but every result points back to raw nodes and raw edges
```

The unlawful use is:

```text
replace raw graph with SCC condensation
drop singleton SCCs
drop generated or auxiliary nodes before hydration
use the hydrated quotient as the only stored graph
```

Therefore, Arango should store the original `raw_infotree_*` graph first, and
then attach SCC/topology labels to those same raw nodes. Condensation nodes or
topological views may be cached as convenience collections, but never as the
primary compiler-memory graph.

SCC labeling invariant:

```text
raw_nodes_out == raw_nodes_in
raw_edges_out == raw_edges_in
scc labels are added to raw nodes
no SCC pass may delete, merge, rename, or replace raw nodes/edges
strict mode fails if any edge endpoint is missing
```

## Required Split

Keep three graph layers in ArangoDB:

- `ig_nodes`, `ig_edges`: compact retrieval graph for planner context.
- `raw_expr_*`: lossless expression/declaration topology exported from the
  environment.
- `raw_infotree_*`: lossless preserved compiler `InfoTree` memory.

These layers should join back to Lean artifacts:

```text
.olean / ModuleData  -> declaration and environment authority
.ilean               -> reference and source-location sidecar
raw_infotree_*       -> elaboration topology and context fiber
```

The `raw_infotree_*` layer must be **LOSSLESS** relative to the chosen Lean
compiler export. No pruning, no silent omission, no "near-lossless" compromise.
If scale forces a derived view, that view must be a separate projection, not the
raw layer.

Unknown compiler-state fields must not be represented by numeric placeholders.
For example, unresolved context sizes from `PartialContextInfo` are `null` or
absent and must be accompanied by leakage rows. A stored `0` is a factual claim
that Lean exposed a zero-valued measurement, not a substitute for missing data.

The raw layer should use separate collections:

- `raw_infotree_roots`: one row per command/file/module InfoTree root.
- `raw_infotree_nodes`: every InfoTree node emitted by Lean.
- `raw_infotree_edges`: parent/child InfoTree edges preserving order.
- `raw_infotree_contexts`: context payloads/provenance needed to reconstruct or
  replay the node's elaboration setting.
- `raw_infotree_payloads`: term/tactic/widget/message payloads as emitted by the
  exporter, with no semantic normalization.
- `raw_decl_nodes`: every environment declaration admitted by the selected root.
- `raw_expr_nodes`: expression DAG nodes from declaration types and values.
- `raw_expr_edges`: expression-to-expression edges.
- `raw_decl_expr_edges`: declaration-to-expression `HAS_TYPE` and `HAS_VALUE`
  edges.
- `raw_edge_leakage`: projection drops, with class and reason.

## Multi-Label Synonym Representation

Synonyms must not be represented as one untyped alias edge. A synonym component
can carry several labels at once, because the same pair may be simultaneously a
Lean-name alias, a physics-language alias, a notation bridge, and a curated
operator synonym.

Use multi-label metadata on synonym/equivalence components:

- `synonym_component`: every synonym group
- `curated_component`: manually registered in `docs/NameEquivalenceRegistry.json`
- `generated_component`: extracted from the equivalence dictionary analysis
- relation labels such as `curated_alias`, `eq`, `notation_alias`,
  `physics_language`, `lean_name`, `latex_name`, `python_name`, `sympy_name`

For Arango this should be stored as a `labels: [...]` array on synonym nodes or
component documents, plus typed edges to member declarations/names. Retrieval may
use labels to decide whether a synonym is strong enough for context injection.
Truth still requires Lean source and kernel verification.

The retrieval graph may be filtered. The raw graph must not silently drop
generated names, auxiliary declarations, external constants, expression nodes,
or info-tree references. If something is excluded from a projection for size, the
raw layer must still retain it, and the projection exclusion must be recorded as
a row in `raw_edge_leakage` or equivalent metadata.

Lossless for the InfoTree layer means:

- every exported InfoTree root is represented
- every exported InfoTree node is represented
- every parent/child edge is represented with sibling order
- every source span, command span, file/module/import provenance, and node kind
  emitted by the exporter is represented
- every payload emitted by the exporter is represented without semantic rewrite
- hydration labels are added only after preservation
- aliases/synonyms are added only after preservation
- every projection drop is auditable as metadata, never silent

## Known Current Loss Points

- `lean/DAG/Indexer.lean` excludes generated/unstable names such as `._`,
  `match_`, `proof_`, and `injEq`.
- `Indexer.lean` drops edges whose endpoints are not both in the filtered node
  set; those losses are summarized in `artifacts/dag/index/edge-leakage.json`.
- `lean/DAG/BlockExport.lean` separates primary and auxiliary declarations.
- Block export reads info-tree dependencies per command snapshot, not as a
  complete global expression graph.
- `tools/leantrail/adapters.py` exports `ig_nodes`/`ig_edges` from a snapshot,
  but does not make those collections equivalent to raw expression memory.
- `tools/infra/arango_gravity_context.py` defaults to declaration/source-excerpt
  retrieval and therefore intentionally ignores many raw graph nodes.

## Immediate Audit

Run:

```bash
python3 tools/infra/arango_fidelity_audit.py \
  --json-out artifacts/leantrail/arango_fidelity_audit.json
```

The report compares local graph artifacts, live Arango counts, and known edge
leakage. Its verdict should decide whether the planner can trust the retrieval
projection for a task or must fall back to raw owner-source and info-tree export.

## Expression Export / Hydrate / Ingest Lane

This lane is useful, but it is not the lossless InfoTree archive. It exports
raw declaration/expression topology from the environment and can be used as an
overlay or search accelerator.

Export raw compiler topology:

```bash
lake env lean --run lean/DAG/ExprArangoExport.lean \
  InfoGeometry.All \
  InfoGeometry \
  artifacts/expr-graph/arango \
  0 \
  true \
  true
```

Arguments:

- `0`: no declaration cap
- first `true`: include external declaration references
- second `true`: include generated declarations

Hydrate topology labels:

```bash
python3 tools/infra/hydrate_arango_topology.py \
  --input-dir artifacts/expr-graph/raw-lossless \
  --output-dir artifacts/expr-graph/raw-lossless-hydrated \
  --raw-layer-policy LOSSLESS \
  --raw-node-collection raw_info_nodes \
  --topology-overlay-collection topology_overlay \
  --strict-lossless
```

Ingest into layered Arango collections:

```bash
python3 tools/infra/arango_layered_ingest.py \
  --input-dir artifacts/expr-graph/raw-lossless-hydrated \
  --raw-nodes-collection raw_info_nodes \
  --raw-edges-collection raw_info_edges \
  --overlay-nodes-collection topology_overlay \
  --overlay-edges-collection topology_overlay_edges \
  --drop-existing
```

These raw expression collections are topology evidence, not the final InfoTree
authority. The final authority is the future `raw_infotree_*` collection family.
`ig_nodes` and `ig_edges` remain compact retrieval projections only.

## Raw DAG Lossless Layer

The DAG indexer now emits two edge layers:

- `artifacts/dag/index/raw_edges.jsonl`: every dependency edge discovered before
  endpoint filtering.
- `artifacts/dag/index/edges.jsonl`: filtered retrieval/projection edge layer.

The raw-DAG layer is not the full Lean compiler `InfoTree`, but it is now
lossless relative to the dependency edges discovered by the indexer. Use it as
the current topology-preserving Arango substrate while the final
`raw_infotree_*` exporter is still being built.

Refresh the DAG index:

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json \
  --refresh
```

Materialize the layered Arango JSONL. This creates a **raw DAG** layer, not a
`raw_infotree_*` layer:

```bash
python3 tools/infra/materialize_lossless_infotree.py \
  --input-dir artifacts/dag/index \
  --output-dir artifacts/infotree/arango-lossless-dag \
  --raw-nodes-collection raw_info_nodes \
  --raw-edges-collection raw_info_edges \
  --overlay-nodes-collection topology_overlay \
  --overlay-edges-collection topology_overlay_edges
```

Expected invariant:

```text
raw_edge_count == raw_edge_docs
raw_edges_preserved_one_for_one == true
```

Ingest into the layered Arango collections:

```bash
python3 tools/infra/arango_layered_ingest.py \
  --input-dir artifacts/infotree/arango-lossless-dag \
  --raw-nodes-collection raw_info_nodes \
  --raw-edges-collection raw_info_edges \
  --overlay-nodes-collection topology_overlay \
  --overlay-edges-collection topology_overlay_edges \
  --drop-existing \
  --json-out artifacts/infotree/arango-lossless-dag/ingest_report.json
```

Verify descent from raw topology to SCC overlay and back to raw witnesses:

```bash
python3 tools/infra/verify_layered_arango_descent.py --json
```

This check picks a raw edge, follows its raw node to the SCC overlay through a
`member_of_scc` projection edge, finds the corresponding `scc_quotient` edge,
and verifies that the quotient multiplicity equals the raw witness query count.

## Layered Arango Network

Arango should represent topology as a layered graph, not as a destructive single
graph. The shape is:

```text
raw_infotree layer
  raw_infotree_nodes
  raw_infotree_edges

raw_expr layer
  raw_expr_nodes
  raw_expr_edges

topology overlay layer
  topology_overlay nodes:
    scc_component
    topo_layer
    dominator_region
  topology_overlay edges:
    member_of_scc
    scc_quotient

retrieval projection layer
  ig_nodes
  ig_edges
```

The topology overlay is coarse-graining that preserves topology by keeping
membership and witness links back to raw topology. It behaves more like a
tensor-labeled network or bigraph than a flat dependency graph:

- raw layer preserves compiler truth
- overlay layer gives structural coordinates
- synonym/alias layer gives naming coordinates
- retrieval layer gives fast prompt context

`tools/infra/hydrate_arango_topology.py` writes this overlay as:

- `topology_overlay_nodes.jsonl`
- `topology_overlay_edges.jsonl`

Every raw edge remains preserved one-for-one in the raw edge collection. Every
SCC component stores its raw `members`. Every membership edge points from a raw
node to an SCC component with role `member_of_scc`. Every SCC quotient edge
points between SCC components with role `scc_quotient` and carries
`witness_raw_edge_keys`. This is lawful coarse-graining: quotient for
navigation, raw graph for truth.

The intended edge descent is:

```text
raw_info_nodes/<decl-or-expr> --member_of_scc--> topology_overlay/scc_N
topology_overlay/scc_A --scc_quotient{witness_raw_edge_keys}--> topology_overlay/scc_B
```

The quotient edge is never sufficient evidence by itself. It is a cached
topological relation whose authority is the list of raw witness edges and the
preserved raw graph.

## SCC-Anchored Retrieval

Topology must not overpower lexical relevance. On the full raw dependency graph,
unbounded propagation over high-degree regions can drift away from the theorem
surface that caused the query.

The retrieval rule is:

```text
lexical/synonym match -> anchored SCC(s) -> bounded quotient expansion -> raw witness descent
```

The anchor is the SCC, not an arbitrary high-degree node. SCC labels provide the
coarse location; `scc_quotient` edges provide controlled neighborhood expansion;
`witness_raw_edge_keys` provide descent back to exact raw evidence.

Unanchored SCC propagation is not permitted for theorem-factory context
injection. If no strong lexical/synonym anchor exists, the correct result is a
miss or a proof-local Lean/mathlib investigation, not injection of unrelated
high-mass topology.

## InfoTree Preservation Requirement

Before calling Arango "faithful", add a Lean exporter that walks
`commandState.infoState.trees` and writes every InfoTree node and child edge
losslessly into JSONL. The exporter must not filter by generated names,
declaration kind, source availability, namespace-derived "importance", or
semantic relevance.

Hydration is then a second pass:

```text
raw_infotree_*  --lossless preservation-->
hydration metadata / topology labels / aliases / retrieval views
```

Search must prefer the hydrated topology labels, but every hit must point back
to a preserved raw InfoTree node.

The concrete contract is maintained in
[`RAW_INFOTREE_EXPORT_CONTRACT.md`](RAW_INFOTREE_EXPORT_CONTRACT.md).

Current stage probe:

```bash
lake env lean --run lean/DAG/RawInfoTreeExport.lean \
  lean/InfoGeometry/Meta/CompilerTelemetry.lean \
  artifacts/raw-infotree/probe

python3 tools/infra/validate_raw_infotree_export.py \
  --input-dir artifacts/raw-infotree/probe \
  --json-out artifacts/raw-infotree/probe_validation.json

python3 tools/infra/validate_raw_infotree_export.py \
  --input-dir artifacts/raw-infotree/probe \
  --require-lossless
```

The probe is loss-audited, not yet fully lossless. It preserves emitted
root/node/child-edge topology and writes leakage rows for payload/context
surfaces that are not yet serialized. The `--require-lossless` command must
fail until `fully_lossless=true` and leakage is zero.

## Operational Rule

Use Arango in this order:

1. Query the compact graph with synonym expansion for fast gravitational context.
2. If the result is missing an expected connection, inspect `edge-leakage.json`
   and raw info-tree/expression artifacts.
3. If the connection exists only in raw compiler memory, promote it into the
   faithful raw Arango layer before using it as theorem-factory context.
4. Only Lean/lake decides truth.
