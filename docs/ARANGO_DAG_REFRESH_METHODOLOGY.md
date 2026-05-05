# Arango DAG Refresh Methodology

> Status: operational runbook
> Scope: refreshed Lean declaration DAG, layered Arango raw/overlay ingest, and SCC-first navigation overlays
> Proof rule: Arango is navigation and audit infrastructure. Lean files and `lake build` remain proof authority.

This document records the exact methodology used to refresh the derived Arango
DAG from the Lean repository. It is intentionally script-by-script: the goal is
to make the database rebuild reproducible without relying on chat memory.

## Skill and Discipline Used

The workflow follows the `arango-dag-operator` discipline:

- start from the coarse SCC/component graph for navigation;
- preserve raw DAG witnesses one-for-one before using overlays;
- treat connectedness, motifs, dominators, process flow, Hodge, Dirac, and
  chiral rows as derived audit signals only;
- descend from any graph claim back to raw Lean declarations before encoding a
  theorem;
- never treat graph proximity as proof.

The practical order is:

```text
Lean DAG export
  -> raw DAG materialization
  -> layered Arango ingest
  -> raw-to-SCC descent verification
  -> SCC-first algorithm overlays
  -> optional faithful retrieval checks
```

## 1. Refresh the Lean Declaration DAG

Run the repository-owned Lake script:

```bash
lake script run dagRefresh
```

This performs the focused build/export path and writes the declaration graph
artifacts under:

```text
artifacts/dag/index/
artifacts/dag/full_graph.json
artifacts/dag/structural-topology.json
```

For the run documented here, the indexer reported:

```text
decls:      55,008
raw edges:  2,131,863
kept edges:   383,546
morphisms:      5,582
```

The indexer may report filtered-edge drops for endpoints outside the filtered
declaration set. That is not an ingest failure. The raw edge layer is handled in
the next step.

## 2. Materialize the Lossless Raw DAG Arango Layer

Materialize the Arango-shaped raw DAG and topology overlay artifacts:

```bash
python3 tools/infra/materialize_lossless_infotree.py \
  --input-dir artifacts/dag/index \
  --output-dir artifacts/infotree/arango-lossless-dag \
  --raw-nodes-collection raw_info_nodes \
  --raw-edges-collection raw_info_edges \
  --overlay-nodes-collection topology_overlay \
  --overlay-edges-collection topology_overlay_edges
```

Important invariant:

```text
raw_edges_preserved_one_for_one == true
raw_edge_count == raw_edge_docs
```

For the run documented here, materialization produced:

```text
raw_node_docs:                    64,425
raw_edge_docs:                 2,131,863
overlay_node_docs:                64,425
overlay_edge_docs:             2,196,288
raw_edges_preserved_one_for_one: true
```

This is a lossless raw DAG dependency layer. It is not a claim that full Lean
compiler InfoTree state has been preserved.

## 3. Add Filename Shims Expected by the Current Ingest Script

The materializer writes:

```text
infotree_raw_nodes.jsonl
infotree_raw_edges.jsonl
topology_overlay_nodes.jsonl
topology_overlay_edges.jsonl
```

The current `arango_layered_ingest.py` script imports raw files named:

```text
decls.jsonl
edges.jsonl
```

Until the script is updated to accept explicit raw artifact filenames, create
local symlinks in the materialized output directory:

```bash
ln -sf infotree_raw_nodes.jsonl artifacts/infotree/arango-lossless-dag/decls.jsonl
ln -sf infotree_raw_edges.jsonl artifacts/infotree/arango-lossless-dag/edges.jsonl
```

Without these shims, only the topology overlay files are ingested and
`verify_layered_arango_descent.py` will fail with:

```text
no raw_info_edges rows found
```

## 4. Ingest Raw and Overlay Layers into Arango

Use the module entrypoint so repo-relative imports resolve cleanly:

```bash
python3 -m tools.infra.arango_layered_ingest \
  --input-dir artifacts/infotree/arango-lossless-dag \
  --raw-nodes-collection raw_info_nodes \
  --raw-edges-collection raw_info_edges \
  --overlay-nodes-collection topology_overlay \
  --overlay-edges-collection topology_overlay_edges \
  --drop-existing \
  --json-out artifacts/infotree/arango-lossless-dag/ingest_report.json
```

If this is run from a restricted sandbox, localhost Arango access may require
approval/escalation. A successful full ingest reports all four collections:

```text
raw_info_nodes=64425
raw_info_edges=2131863
topology_overlay=64425
topology_overlay_edges=2196288
```

The `--drop-existing` flag intentionally replaces the derived Arango layer with
the freshly materialized artifact set. It does not modify Lean source files.

## 5. Verify Raw-to-SCC Descent

Run the descent verifier:

```bash
python3 -m tools.infra.verify_layered_arango_descent --json
```

The verifier samples a raw edge, maps both endpoints through `member_of_scc`,
finds the corresponding `scc_quotient` edge, and checks that the quotient
multiplicity matches the raw witness query count.

A successful report includes:

```json
{
  "ok": true,
  "witness_count_matches_multiplicity": true
}
```

This is the minimum audit gate before using SCC connectedness as navigation.

## 6. Materialize SCC-First Algorithm Overlays

Run the repo-documented algorithm overlay pass:

```bash
python3 -m tools.infra.arango_dag_algorithms \
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

For the run documented here, the pass wrote:

```text
arango_dag_components:              64,425
arango_dag_component_edges:      1,396,798
arango_dag_layers:                       4
arango_dag_chains:                       4
arango_dag_capstones:                  512
arango_dag_skeleton:                   500
arango_dag_dominators:               5,000
arango_dag_wl_labels:                7,000
arango_dag_motifs:                   1,200
arango_dag_two_complex:              4,634
arango_dag_sources_sinks:           31,285
arango_dag_impact:                    128
arango_dag_process_flows:         100,000
arango_dag_defects:                    84
arango_dag_lawful_paths:            5,000
arango_dag_hodge:                   2,685
arango_dag_chiral:                  1,403
arango_dag_dirac:                   5,124
arango_dag_communities:                42
arango_dag_community_member_edges: 64,425
```

These are derived overlays. They are useful for routing, impact analysis,
dominance questions, motif discovery, and theorem-basin navigation, but they
are not mathematical proofs.

## 7. Optional Faithful Retrieval Check

After ingest and overlays, run a targeted graph-context retrieval to confirm
that the refreshed Arango layer can find the intended corridor:

```bash
python3 tools/infra/arango_gravity_context.py \
  --query 'DIIITopologicalCountExample projective count Drazin probability gauge' \
  --source arango \
  --graph-mode faithful \
  --top-k 12 \
  --max-hops 2 \
  --json-out artifacts/infotree/arango-lossless-dag/projective_count_drazin_context.json
```

Use this only as a retrieval smoke test. If the result suggests a mathematical
connection, descend to the Lean owner files and encode the relation as a real
definition, theorem, or constructive witness.

## Connectedness Semantics

Choose the connectedness question explicitly:

```text
weak connectedness
  ignore direction; asks whether two declarations live in the same theorem basin

forward reachability
  dependency/causal flow from source component to target component

reverse reachability
  impact/users/capstones depending on the seed component
```

Canonical directed reachability shape:

```aql
FOR v, e, p IN 1..20 OUTBOUND @seed arango_dag_component_edges
  OPTIONS { bfs: true, uniqueVertices: "global" }
  FILTER v._id == @target
  LIMIT 1
  RETURN {
    connected: true,
    depth: LENGTH(p.edges),
    path: p.vertices[*]._key
  }
```

Reverse impact:

```aql
FOR v, e, p IN 1..20 INBOUND @seed arango_dag_component_edges
  OPTIONS { bfs: true, uniqueVertices: "global" }
  RETURN {
    component: v._key,
    depth: LENGTH(p.edges),
    layer: v.rep_layer
  }
```

Weak basin search:

```aql
FOR v, e, p IN 1..20 ANY @seed arango_dag_component_edges
  OPTIONS { bfs: true, uniqueVertices: "global" }
  RETURN DISTINCT v._key
```

## Non-Negotiable Proof Boundary

Arango connectedness is navigation, audit, and context assembly. It is not a
Lean proof.

When a graph connection matters mathematically:

1. anchor to a raw declaration or retrieval result;
2. map to its SCC/component;
3. traverse `arango_dag_component_edges` or `topology_overlay_edges`;
4. descend from the SCC path back to raw Lean declarations;
5. read the owner files;
6. replace any vacuous bridge hypothesis with a constructive Lean statement
   or a narrowed, honest witness field.

That last step is where theorem work happens.
