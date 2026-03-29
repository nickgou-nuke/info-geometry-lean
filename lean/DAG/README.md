# DAG Subsystem

`lean/DAG/` is the Lean-side graph export layer for this repository.
It is not the sole owner of architectural grammar anymore; depth legality now starts in:
- [lawful-flow-glossary.md](../../docs/lawful-flow-glossary.md) for constitutive boundary/defect tag semantics
- [Architecture.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Meta/Architecture.lean)
- [Audit.lean](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Audit.lean)

The DAG subsystem exists because this repository is one theory spread across many representation surfaces.
Its job is to externalize memory about ownership, adjacency, transport, and coherence so that context can be recovered after local state is lost.
It is an audit layer for morphisms, not an alternate source of mathematical truth.

## Graph Layers

Keep these graph views distinct:
1. declaration DAG: atomic declaration-to-declaration dependency truth
2. structural topology: SCC condensation, layers, dominators, witness paths
3. source-sink correspondence: packet and carrier incidence built downstream in Python
4. semantic export: heavy-file block structure for frontier work
5. representation-depth overlays: Lean-enforced depth grammar projected onto the authoritative DAG
6. process-flow export: edge-local transport evidence, bounded path candidates, and localized defect rows

## Authoritative Export Path

The declaration graph is refreshed with:

```bash
python3 tools/infra/refresh_decl_graph.py
```

which runs the Lean-side indexer and writes:
- `artifacts/dag/full_graph.json`
- `artifacts/dag/index/decls.jsonl`
- `artifacts/dag/index/edges.jsonl`
- `artifacts/dag/structural-topology.json`

Downstream Python tooling then derives source-sink, causal, theorem-surface, semantic quotient, and representation-depth reports.
Those reports should agree with the Lean-native audit, not replace it.

The constitutive process-flow layer is exported with:

```bash
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
```

This layer is for:
- edge-local transport evidence
- event aggregation over observed edges
- bounded ancestry/path candidates
- localized defect evidence
- derived comparison and cocycle reports downstream

## Trust Order

If graph-derived surfaces disagree, trust:
1. Lean source and the native audit under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
2. `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`
3. `artifacts/dag/structural-topology.json`
4. `artifacts/dag/source-sink-bipartite.json`
5. `reports/dag/*`

## Current Anchor Corridor

The current long chain that should remain visible in the declaration DAG and the causal reports is:
- `PositiveMeasure -> Projective.Normalize -> PositiveRayCore -> RelativePotentialCore -> RelativePotentialCountBridge -> RelativeSurprisalOperatorLift`

The important point is not only depth. It is that the chain now contains a real owned cocycle at each adjacent rise:
- representative normalization cocycle
- count specialization cocycle
- raw operator cocycle
- averaged modular-Hamiltonian cocycle

The DAG layer should preserve that owner corridor and distinguish it from thinner reprojection tails above it.

## Intended Use

Use the DAG subsystem for:
- causal order and rooted structure
- owner and dependency analysis
- theorem-surface and shell pressure analysis
- representation-depth legality and bicategorical reporting
- process-flow transport and coherence pressure reporting

Use it to recover memory and choose the next file to read.
Do not use it to delete mathematics without reading the owner code.

Do not use a single hotspot heuristic as the whole theory map.
