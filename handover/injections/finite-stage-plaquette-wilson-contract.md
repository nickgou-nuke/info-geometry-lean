# Ground-truth theorem contract: finite-stage plaquette / Wilson bridge (Phase 5 first slice)

## Claim

Instantiate the repository's generic Wilson-loop / causal-flow lens on the
finite-stage carrier: with `Op := Stage n` (`InfoGeometry.Clifford.Cl11TensorTowerLimit`,
`Algebra ℝ Limit` at line 143), a detailed-balance cut flow, and the staged
exact-connection owner `InfoGeometry.Canonical.TensorStageExactConnection`,
the flow-Wilson readout of the elementary plaquette collapses to zero
curvature, via the owned detailed-balance theorem.

## Carrier and conventions

- `Stage n` is the staged carrier of `TensorStageExactConnection`; ring
  operations are the tower's own; linearity/scalar field is `ℝ`.
- A cut is an idempotent `P : Stage n` supplied by the existing staged-cut /
  Phase-4 carrier-map owner (`PeirceToMatrixConnectionCarrierMap`), not by a
  new definition.
- The flow packet is the owned generic
  `ThermodynamicGauge.CausalNonequilibriumFlow Op` with fields
  `P_forward`, `P_backward`, `d_ln_Q` and the detailed-balance condition
  `flow.P_forward * flow.P_backward = flow.P_backward * flow.P_forward`
  (`entropy_production_eq_zero_iff_detailed_balance`,
  `Topology/ThermodynamicGauge.lean:49`).

## Source-confirmed declarations (deep-searched 2026-11-03)

- `Topology/ThermodynamicGauge.lean`: `CausalNonequilibriumFlow` (17),
  detailed-balance commutation fields (31, 36), detailed-balance
  characteristic (49).
- `Topology/WilsonLoopThermodynamics.lean` `[Ring Op]` generic lens:
  `LoopWord` (23), `flowed_connection_step` (26), `finite_flow_connection_word`
  (30), `finite_flow_wilson_loop` (35), `LoopWord.holonomy` (41),
  `LoopWord.flowHolonomy` (45) with `nil`/`singleton` simp lemmas (67–99);
  `curvatureReadout` (`BostConnesWilsonLoop.lean:28`) with
  `curvatureReadout_eq_zero_of_detailed_balance` (51) and
  `curvatureReadout_smul` (60).
- `Canonical/TensorStageExactConnection.lean`: `stageEmbed_exactCovariantDerivative`
  (47), `bondMap_exactCovariantDerivative` (62), `exactCutCurvature` (97),
  `exactCutCurvature_apply` (103), `stageEmbed_exactCutCurvature` (113),
  `bondMap_exactCutCurvature` (121), `ofStage_exactCutCurvature_bond` (149).

## Smallest source-confirmed gap

No declaration instantiates the generic flow/Wilson lens at `Op := Stage n`
and links the staged cut curvature `exactCutCurvature` to the flow-Wilson /
curvature readouts. The plan doc's Phase 5 row ("plaquette curvature, Wilson
loops, or lattice gauge covariance on the finite stages") is stale: the generic
word/holonomy lens exists, only the finite-stage instantiation is open.
Designated owner file:
`lean/InfoGeometry/Canonical/FiniteStagePlaquetteWilson.lean`.

## First slice (staged, genuinely small theorems)

Owner ship note: the flow packet has four fields `⟨Q, d_ln_Q, P_forward,
P_backward⟩` and carries *no* detailed-balance field — so the slice derives
balance from the cut-corner algebra itself, which is stronger than the
original sketch suggested.

1. `cutProducts (hP : P * P = P) : P * (1 - P) = 0 ∧ (1 - P) * P = 0` — the
   pure idempotent-corner algebra.
2. `cutFlow (P Q d : Stage n) : CausalNonequilibriumFlow (Stage n)` with
   `P_forward := P`, `P_backward := 1 - P`, plus
   `cutFlow_entropy_production_zero (hP)` discharging
   `entropy_production (cutFlow P Q d) = 0` from slice 1, and
   `cutFlow_detailed_balance` transferring it through the owned
   `entropy_production_eq_zero_iff_detailed_balance`.
2. `stage_flow_wilson_singleton` — restage of the owned singleton lemma at
   `Op := Stage n`: `finite_flow_wilson_loop flow [s] = 1 + P_forward * s * P_backward`.
3. `stage_plaquette_curvature_zero` — the generic curvature readout of the
   elementary two-bond plaquette vanishes under detailed balance:
   `curvatureReadout τ (flow-wilson plaquette word) = 0`, discharged by the
   owned `curvatureReadout_eq_zero_of_detailed_balance` at `Op := Stage n`.

## Adjacent claims not established

No plaquette *dynamics*, no lattice size growth, no continuum limit, no
KMS/thermal statement. The凝 slice is a finite-level, ring-and-word algebra
instantiation; any step growth or limit must go through the existing
inductive-colimit owner row (Phase 7) and is out of scope here.
