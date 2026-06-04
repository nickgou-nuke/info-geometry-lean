# Shadow Cones — Boundary Cochains on the Proof DAG

A shadow is not merely "missing proof debt." It is an unintegrated apex of a
causal cone on the proof dependency graph.

## Model

```
Shadow = boundary cochain seeking a filler.
```

A shadow has partial incidence to the existing proof graph — past incidences
(dependencies that support it) and future incidences (declarations it blocks).
It is not yet a node in Logos, but it already has coboundary data.

## Lifecycle

```
Black Book conjecture
    ↓
roaming shadow (no incidence)
    ↓ incidence search
incident shadow (one-sided incidence)
    ↓ paired with de Bruijn / InfoTree nodes
paired shadow (two-sided incidence)
    ↓ proof attempt
integrated theorem OR explicit open debt
```

## Formalization

- `lean/InfoGeometry/SelfReference/ShadowCone.lean` — Lean structures:
  - `ShadowKind` (sorryDebt, missingPremise, overclaimedBridge, archetypeRecurrence,
    failedSynthesis, boundaryAnalogy, roamingConjecture)
  - `ShadowStatus` (roaming, incident, paired, integrated, rejected)
  - `ShadowCone(α)` — apex name, kind, status, past/future boundaries, obstruction

- `tools/infra/shadow_cone_scanner.py` — Python scanner:
  - Extracts `:= by sorry` declarations
  - Computes past/future incidences from dependency graph
  - Scores attachment (roaming/incident/paired)
  - Outputs JSONL for ArangoDB ingestion

## Current Status

| Status | Count | Description |
|--------|-------|-------------|
| roaming | 0 | No incidence detected |
| incident | 107 | One-sided incidence |
| paired | 7 | Two-sided incidence |
| integrated | 0 | Formally resolved |

Top shadows by priority:

| File | Apex | Score |
|------|------|-------|
| `Eval/SorryFillerTest.lean` | `has` | 350 |
| `Krein/HodgeStarOperator.lean` | `on` | 345 |
| `OperatorAlgebra/HorizonKMS.lean` | `observed_heat_ne_zero...` | 250 |
| `OperatorAlgebra/SusceptibilityHessian.lean` | `IsHessianDegenerate` | 250 |

## Integration with the Cognitive Architecture

```
Scan ──► ShadowCone ──► ArangoDB ──► Worker ──► Proof attempt
  │           │              │            │
  │    past/future      queue tasks    GEPA evolve
  │    incidences                      ChatGPT audit
  │                                    Pi/DeepSeek
  │
  └── LeanTrail DAG ──► dependency graph
```
