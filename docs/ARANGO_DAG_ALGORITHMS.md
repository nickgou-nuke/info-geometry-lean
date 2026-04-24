# Arango DAG Algorithms

`tools/infra/arango_dag_algorithms.py` runs classical graph algorithms over the
live Arango SCC quotient overlay and writes the result as a separate derived
overlay.

It does not mutate:

- `raw_info_nodes`
- `raw_info_edges`
- `topology_overlay`
- `topology_overlay_edges`

It writes only:

- `arango_dag_components`
- `arango_dag_component_edges`
- `arango_dag_layers`
- `arango_dag_chains`
- `arango_dag_capstones`
- `arango_dag_skeleton`
- `arango_dag_layer_flows`
- `arango_dag_dominators`
- `arango_dag_wl_labels`
- `arango_dag_motifs`
- `arango_dag_two_complex`
- `arango_dag_sources_sinks`
- `arango_dag_impact`
- `arango_dag_process_flows`
- `arango_dag_defects`
- `arango_dag_lawful_paths`
- `arango_dag_hodge`
- `arango_dag_chiral`
- `arango_dag_dirac`
- `arango_dag_morphism_candidates`
- optional named graph `arango_dag`

The overlay is navigation data, not Lean proof authority.

## Navigation-only authority boundary

Use the DAG overlay to answer questions such as:
- which SCC basin currently owns a bridge pressure,
- whether there is an existing owner path worth descending into,
- which upstream/downstream owner surfaces should be inspected next,
- where the nearest lawful raw witnesses live.

Do not use the overlay to answer questions such as:
- whether a theorem is true,
- whether a bridge closes mathematically,
- whether graph proximity is itself semantic proof,
- whether an SCC path can discharge a Lean obligation.

Operational rule:

```text
Arango/DAG answers navigation and basin-ownership questions.
Lean answers typing, hypotheses, proof, and closure questions.
```

The DAG layer is therefore a descent planner and mass locator, not a theorem
oracle.

## Source Graph

Default source:

```text
topology_overlay
topology_overlay_edges(role == "scc_quotient")
```

This is the SCC quotient graph produced from the Lean raw-DAG dependency layer.
It is not the full compiler `InfoTree`.

## Algorithms

The current pass computes:

- deduplicated SCC quotient edges with summed multiplicity
- topological order and cyclic-residue check
- dependency roots, matching `DAG.Analysis.rootSet`
- capstones, matching `DAG.Analysis.capstoneSet`
- minimum and maximum depth from dependency roots over reverse dependency flow
- optional dominator counts using integer bitsets
- optional seed reachability and path-count summaries
- topological layer rows, matching the `RootOrderExport` layer view
- representative deepest root chains, matching `Analysis.deepestRootChains`
- bounded capstone ancestry summaries
- theory skeleton rows using the `Analysis.extractTheorySkeleton` scoring shape
- component-level L0-L5 layer histograms derived from raw member declarations
- edge-level layer flow, polarity, and regressive-flow flags
- aggregate `L_i -> L_j` flow rows in `arango_dag_layer_flows`
- stable Weisfeiler-Lehman hashes over SCC components
- bounded motif/subgraph matching for squares/diamonds, spans, cospans,
  triangles, and forks
- optional dominator-set rows, with mask persistence only when explicitly
  requested
- bounded two-complex edge/face materialization
- bounded `d1*d2 = 0`, Euler, GF(2) rank, Betti, and Hodge/Dirac dimension
  proxies
- first-class source/sink/capstone rows
- seed-centered forward/reverse impact rows
- `ProcessFlowExport`-style dependency role, boundary, locality, polarity,
  and defect rows
- direct/two-step lawful path candidates with defect cost
- bounded sparse Hodge `L0` rows
- bounded sparse graph Dirac rows
- chiral grading rows and anticommutation violation counts

Full dense Hodge matrices are intentionally not built for million-edge graphs.
Full root-by-capstone path ancestry is also intentionally bounded; the current
live graph has thousands of roots and capstones, so an unbounded all-pairs pass
would be a deliberate performance regression.

## DAG-To-Arango Algorithm Coverage

| Lean DAG algorithm | Arango-DAG implementation | Boundary |
| --- | --- | --- |
| `Basic` graph model | `arango_dag_components` + `arango_dag_component_edges` | Derived from SCC quotient overlay; raw graph remains untouched. |
| `Topo` order | Implemented | Fails closed if cyclic residue appears. |
| `Analysis.rootSet` / `capstoneSet` | Implemented | Uses quotient edge orientation from the live overlay. |
| `Analysis.depthFromRoots` / longest chains | Implemented | `depth_min`, `depth_max`, and `depth_spread` are persisted per component. |
| `Analysis.rootContributionCounts` | Bounded | Full all-root/all-capstone ancestry is intentionally not run by default. |
| Dominator counts | Implemented | Full bitset masks are available only with `--write-dominator-masks`. |
| Full dominator sets | Bounded/persistable | `arango_dag_dominators`; default persists counts and metadata for a bounded prefix. |
| L0-L5 representation flow | Implemented | `dominant_rep_layer`, edge polarity, and aggregate layer-flow rows. |
| Theory skeleton extraction | Implemented as score-compatible overlay | Navigation signal, not theorem evidence. |
| Isomorphism/WL hashing | Implemented | Stable BLAKE2 hash labels over labeled in/out neighborhoods. |
| Subgraph motifs | Implemented, bounded | Squares/diamonds, spans, cospans, triangles, forks. |
| Two-complex vertices/edges/faces/digons | Implemented, bounded | Materializes cells in `arango_dag_two_complex` for the selected basin. |
| Boundary matrices | Implemented as sparse GF(2) bitsets | Summarized by rank and explicit edge/face boundary rows. |
| `boundarySquaredZero` | Implemented, bounded | Checks `d1*d2 = 0` over GF(2) on the selected two-complex. |
| Euler characteristic | Implemented, bounded | `V - E + F` for the selected two-complex. |
| Gaussian rank / Betti | Implemented, bounded | GF(2) sparse rank, not full rational dense rank. |
| Hodge Laplacians / Dirac / chiral checks | Proxy only | Stores trace/dimension proxies; full sparse operator checks should be opt-in or GPU-backed. |
| Process-flow roles/defects | Implemented, bounded | Ports the Lean taxonomy to SCC edges using L0-L5 layer metadata. |
| Sources/sinks/causal impact | Implemented | Source/sink rows plus seed-centered forward/reverse impact rows. |
| Sparse Hodge/Dirac/chiral operators | Implemented, bounded | Stores `L0`, Dirac sparse block entries, chiral signs, and violation counts for selected basin. |
| Exact morphism / `isDefEq` checks | Not Arango authority | Arango can prefilter candidates; Lean must verify. |
| Category/functor identity/composition checks | Not Arango authority | Arango can store candidate quivers/witness paths; Lean must prove exactness. |

## L0-L5 Flow Control

Layer labels are lifted from raw SCC members into each component:

- `rep_layer_counts`
- `dominant_rep_layer`
- `dominant_rep_depth`

Component edges receive:

- `source_layer`
- `target_layer`
- `layer_flow`, e.g. `L4_ModularTransport->L5_ThermodynamicClosure`
- `flow_polarity`: `ascending`, `same_layer`, `descending_adjacent`,
  `regressive`, or `unlabeled`
- `regressive`

Unlabeled flow remains explicit. It is not silently treated as lawful.

## Commands

Dry run:

```bash
python3 tools/infra/arango_dag_algorithms.py \
  --json-out artifacts/infotree/arango_dag_algorithms_dry_report.json
```

Write the overlay and named graph:

```bash
python3 tools/infra/arango_dag_algorithms.py \
  --compute-dominators \
  --seed-representative RouterDefectBoundBridge \
  --wl-limit 7000 \
  --motif-max-nodes 1500 \
  --two-complex-max-nodes 7000 \
  --two-complex-max-edges 200000 \
  --two-complex-cell-limit 10000 \
  --process-flow-limit 100000 \
  --lawful-path-limit 5000 \
  --hodge-sparse-limit 20000 \
  --write \
  --drop-existing \
  --create-named-graph \
  --graph-name arango_dag \
  --json-out artifacts/infotree/arango_dag_algorithms_named_graph_report.json
```

## How To Use The Overlay

Use `arango_dag` for graph analysis and navigation over the SCC coarse-grained
theory graph. Do not use it as proof authority.

Operational rule for theorem work:

```text
Arango-DAG signal
-> raw Lean owner surface
-> explicit Lean context/witness structure
-> theorem proved under that context
-> lake/Lean validation
```

Do not generalize from graph proximity, process-flow defects, layer-flow, or
Hodge/chiral signals into an unconditional theorem. If a graph signal suggests a
relationship, encode the required hypotheses explicitly, as with context objects
such as `SouriauDensityWeightContext` or `KKTChiralContext`, and prove only what
that context supports.

Recommended workflow:

1. Refresh/load the faithful raw-DAG SCC overlay first.
2. Run `arango_dag_algorithms.py` as a derived overlay pass.
3. Query `arango_dag_*` collections for planning, audit, and candidate paths.
4. Descend to raw witnesses through `topology_overlay_edges`.
5. Verify mathematical claims in Lean.

Typical investigation path:

```text
query concept
-> SCC anchor
-> arango_dag_components / arango_dag_process_flows
-> defects / lawful paths / motifs / Hodge basin
-> raw witness descent
-> Lean module check
```

For closure-debt work, prefer this order:

- Use `arango_dag_process_flows` to find regressive, remote, mixed, or boundary
  bypass edges.
- Use `arango_dag_defects` to rank audit targets by defect cost.
- Use `arango_dag_sources_sinks` to identify owner roots and capstone sinks.
- Use `arango_dag_impact` from a seed theorem to scope local blast radius.
- Use `arango_dag_motifs` for square/diamond/span/cospan candidates.
- Use `arango_dag_hodge`, `arango_dag_chiral`, and `arango_dag_dirac` only on
  bounded SCC basins.
- Use `arango_dag_morphism_candidates` only as a staging area for Lean
  `isDefEq` checks.

Useful AQL fragments:

```aql
FOR d IN arango_dag_defects
  SORT d.cost DESC
  LIMIT 20
  RETURN d
```

```aql
FOR f IN arango_dag_process_flows
  FILTER f.polarity_class == "regressive"
  LIMIT 20
  RETURN f
```

```aql
FOR h IN arango_dag_hodge
  FILTER h._key == "hodge_summary"
  RETURN h
```

The Hodge/Dirac/chiral rows are intentionally sparse and bounded. On large DGX
Spark runs, raise `--two-complex-max-nodes`, `--two-complex-max-edges`, and
`--hodge-sparse-limit` deliberately. Do not silently switch defaults to dense
full-graph matrices.

## Current Live Checkpoint

The first live pass over `infogeometry` produced:

- `components = 25,947`
- `scc_quotient_rows = 1,184,253`
- `deduplicated_edges = 773,050`
- `topological_order_count = 25,947`
- `cyclic_residue_count = 0`
- `dependency_roots = 6,486`
- `capstones = 7,649`
- `arango_dag_components = 25,947`
- `arango_dag_component_edges = 773,050`
- `arango_dag_layers = 4`
- `arango_dag_chains = 3`
- `arango_dag_capstones = 512`
- `arango_dag_skeleton = 500`
- `arango_dag_layer_flows = 30`
- `arango_dag_dominators = 5,000`
- `arango_dag_wl_labels = 7,000`
- `arango_dag_motifs = 1,200`
- `arango_dag_two_complex = 4,243`
- `arango_dag_sources_sinks = 14,135`
- `arango_dag_impact = 118`
- `arango_dag_process_flows = 100,000`
- `arango_dag_defects = 36`
- `arango_dag_lawful_paths = 5,000`
- `arango_dag_hodge = 2,451`
- `arango_dag_chiral = 1,281`
- `arango_dag_dirac = 4,676`
- `arango_dag_morphism_candidates = 0`

The seed-centered two-complex around
`InfoGeometry.LLM.TrialityMoE.RouterDefectBoundBridge` produced:

- `vertices = 112`
- `edges = 1,169`
- `triangular_faces = 3,073`
- `digon_faces = 0`
- `euler_characteristic = 2,016`
- `rank_boundary1_mod2 = 111`
- `rank_boundary2_mod2 = 1,058`
- `betti0_mod2 = 1`
- `betti1_mod2 = 0`
- `boundary_squared_zero_mod2 = true`
- `cell_rows_materialized = 4,242`
- `cell_rows_truncated = false`

The same seed basin produced sparse Hodge/Dirac/chiral rows:

- `laplacian0_sparse_entries = 2,450`
- `trace_laplacian0 = 2,338`
- `dirac_dim = 1,281`
- `chiral_anticommutation_violations = 0`

The process-flow overlay is derived from the L0-L5 layer metadata. It is an
audit layer: defect rows identify candidates for review, not proof failures by
themselves.

The `arango_dag` named graph traverses through
`arango_dag_component_edges` and carries the layer/chain/capstone/skeleton
collections as orphan collections.

The live layer-flow pass exposed regressive buckets such as:

- `L4_ModularTransport -> L2_Operator`
- `L5_ThermodynamicClosure -> L2_Operator`
- `L5_ThermodynamicClosure -> L1_Projective`
- `L5_ThermodynamicClosure -> L3_Krein`

These are control-surface signals for audit, not automatic errors.

With seed `RouterDefectBoundBridge`, the live pass reported:

- `downstream_reachable = 9`
- `upstream_reachable = 107`
- `downstream_path_sum = 9`
- `upstream_path_sum = 1169`

## Truth Boundary

If an Arango DAG result disagrees with the Lean-produced topology, Lean wins.
The Arango overlay is useful for fast navigation, ranking, and external graph
analytics. It is not theorem evidence unless descended back to raw witnesses and
checked by Lean/lake.
