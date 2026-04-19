# Arango Layered Tensor Overlay

Status: implementation note for the topology-preserving layered graph model.

Invariant
- Raw InfoTree / raw expr graph is preserved exactly first.
- Overlay layers are additive, never replacements.
- Every coarse relation must descend through explicit witnesses.

Layers
1. Raw layer
- Collections:
  - `raw_infotree_nodes`
  - `raw_infotree_edges`
- Contract:
  - raw nodes preserved one-for-one
  - raw edges preserved one-for-one
  - provenance and payload remain evidentiary

2. Topology overlay layer
- Collections:
  - `topology_overlay`
  - `topology_overlay_edges`
- SCC nodes live here as coarse-grained quotient objects.
- Overlay does not mutate or delete raw topology.

Edge roles
- `member_of_scc`
  - projection edge from raw node -> SCC node
  - descent path from quotient object back to source truth
- `scc_quotient`
  - quotient edge between SCC nodes
  - must carry `witness_raw_edge_keys`

Ontology
- This is not graph simplification.
- It is stratified topology-preserving coarse graining.
- The model is a layered tensor network / bigraph-style structure:
  - fine-grain raw topology
  - coarse quotient topology
  - cross-layer projection edges

Current tooling
- `tools/infra/hydrate_arango_topology.py`
  - computes SCC overlay and labels raw nodes/edges with layer/grain metadata
  - emits:
    - `ig_nodes.jsonl`
    - `ig_edges.jsonl`
    - `topology_overlay_nodes.jsonl`
    - `topology_overlay_edges.jsonl`
- `tools/infra/ingest_topology_overlay.py`
  - ingests raw and overlay layers into separate Arango collections

Recommended workflow
1. Export raw lossless graph JSONL.
2. Hydrate topology overlay without altering raw edges.
3. Ingest both raw and overlay layers into Arango.
4. Run search/navigation on overlay when useful.
5. Always permit exact descent through raw witnesses.

Search rule
- topology rules search first
- semantic hydration is secondary
- absence from overlay is never proof of absence from raw layer
