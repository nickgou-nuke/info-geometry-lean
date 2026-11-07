# Finite plabic-network lane: QMS intake and child contract

## Intake and disposition

The request to prove that a plabic square move induces the positive
`Gr(2,4)` boundary-measurement exchange is theorem-bearing and currently
**Bucket 3 / R4**. The current owners prove matrix Plücker exchange and a
polynomial Lusztig/Postnikov urban-renewal identity, but do not define a
plabic graph whose boundary measurement is that matrix. The prose-level square
move comparison therefore remains open.

Machine-readable intent envelope:

```json
{
  "concept_id": "plabic-boundary-measurement-square-move",
  "source_text": "Construct a finite planar network, identify its boundary path measurement with the Gr(2,4) chart, and ultimately compare a graph square move with Plucker exchange.",
  "intake_classification": "theorem-bearing",
  "target_status": "conjectural-scaffold",
  "risk_level": "R4",
  "allowed_imports": [
    "Mathlib.Basic.Real.Basic",
    "Mathlib.Tactic.NormNum",
    "Mathlib.Tactic.Linarith",
    "Mathlib.Tactic.Positivity",
    "InfoGeometry.Topology.PlabicBoundaryMeasurement"
  ],
  "formal_objects": [
    "finite directed graph on Fin 4",
    "straight-line drawing in Real x Real",
    "two source-to-sink paths indexed by Fin 2",
    "edge-weight path product and finite boundary path sum"
  ],
  "acceptance_theorems": [
    "the graph has a crossing-free straight-line drawing",
    "the two source-to-sink path sum equals the chart minor Delta_13"
  ],
  "non_theorem_claims": [
    "the graph is a Postnikov plabic graph",
    "a graph square move induces the matrix Plucker exchange",
    "the graph measurement equals the full 2x4 chart",
    "amplituhedron, BCFW, physical unitarity, or spacetime claims"
  ]
}
```

## Ground-truth theorem contract

The child formalization uses the finite directed diamond with vertices
`source`, `upper`, `lower`, `sink` and directed edges
`source → upper → sink` and `source → lower → sink`. Its drawing places these
vertices at `(0,0)`, `(1,1)`, `(1,-1)`, `(2,0)`. Four positive real edge
weights label the directed edges. A path is one of the two middle-vertex
choices, and its weight is the product of its two edge weights.

The target is the exact finite identity

```text
boundaryPathSum = t₁ * t₃ + t₂ * t₄
                = minor2 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) 1 3
```

The graph has an explicit straight-line crossing-freeness proof. This closes
the planar-DAG-to-chart-readout gap only. It does not produce a plabic graph:
there are no internal vertex colors, trivalence, boundary trip permutation,
or Postnikov boundary-measurement convention in this child carrier. Those
remain separate downstream contracts, as do the square-move comparison and
the connection from a mutated chart to the twistor/Zorn two-ray lane.
The module also proves that each route weight and their sum are strictly
positive when all four real edge weights are strictly positive.

## Source trace

- `PlabicBoundaryMeasurement.chartDiamondAdjacency` and
  `chartDiamondGreen_eq_path_sum` give an abstract weighted DAG and its matrix
  path sum, explicitly disclaiming a planar embedding.
- `boundaryMeasurement_plucker_13_eq_diamond_readout` identifies the endpoint
  readout with `Δ₁₃`.
- `mutatePlucker_eq_minor2_of_plucker_relation` proves the matrix exchange
  conditional on a nonzero denominator; its owner explicitly says this does
  not identify a graph move.
- `postnikov_urbanRenewal_mutation_and_bcfw_st_channels` proves a polynomial
  matrix identity and a chart-channel decomposition, not graph measurement.
- `PlabicCluster.mutateF` is an abstract cluster X-mutation on five face
  weights; it does not carry a graph or a boundary measurement map.

## QMS status

The finite child passed its locked compiler and module build, a module-local
axiom check, a heuristic placeholder scan, and a semantic-vacuity scan. Its
QMS run record is `artifacts/qms/T-PLABIC-DIAMOND-20261107-run.md`. Independent
A-A/QA-A review remains outstanding, so this is not final acceptance. Promotion
of the square-move claim requires a separately audited graph carrier and an
explicit comparison map to the chart measurement.
