# D4 Crystal Synthesis: Formalism and Interpretation

This note documents the "algebraic crystallography" thread in three layers.

## Scope / Non-claims

- This document does not assert an ontological claim about physical reality.
- It separates: formal Lean statements, optional interpretation, and
  requirements for physicalization.

## 1. Formal Claims (Lean-verified, auditor-grade)

| Claim | Lean symbol | File | What to check |
| --- | --- | --- | --- |
| Triadic interaction core exists | `InfoGeometry.Canonical.Triality.TriadicCore` | `lean/InfoGeometry/Canonical/Triality.lean` | Structure fields `interact`, `route` |
| Split metric instance is constructed | `InfoGeometry.Canonical.Triality.splitMetricTriadicInstance` | `lean/InfoGeometry/Canonical/Triality.lean` | Definitional equations and `route_norm_compat` |
| Attention residual decomposition | `InfoGeometry.Canonical.Triality.GeometricAttentionMap.attention_decomposition_residual` | `lean/InfoGeometry/Canonical/Triality.lean` | Assumptions (`h_route`, `weights_sum_one`) and conclusion |
| Bregman-softmax coupling | `InfoGeometry.Canonical.BregmanTriality.softmaxBregmanAttention` | `lean/InfoGeometry/Canonical/BregmanTriality.lean` | Type of constructed `GeometricAttentionMap` |
| Update-order hysteresis witness | `InfoGeometry.Canonical.HolographicEmergence.exists_gaugeOrderHysteresis_witness` | `lean/InfoGeometry/Canonical/HolographicEmergence.lean` | Existence statement reducing to `exists_updateOrderHysteresis_n2` |

Related hysteresis primitives:
- `InfoGeometry.Canonical.WeylInformationGauge.UpdateOrderHysteresis`
- `InfoGeometry.Canonical.WeylInformationGauge.exists_updateOrderHysteresis_n2`

### Audit quickstart

```text
grep -R "structure TriadicCore" lean/InfoGeometry/Canonical/Triality.lean
grep -R "attention_decomposition_residual" lean/InfoGeometry/Canonical/Triality.lean
grep -R "softmaxBregmanAttention" lean/InfoGeometry/Canonical/BregmanTriality.lean
grep -R "exists_gaugeOrderHysteresis_witness" lean/InfoGeometry/Canonical/HolographicEmergence.lean
grep -R "exists_updateOrderHysteresis_n2" lean/InfoGeometry/Canonical/WeylInformationGauge.lean
```

## 2. Physical / Metaphorical Interpretation (optional)

This layer uses physics language to interpret formal structure, without claiming
that the universe must realize it.

- Triality/QKV-style routing can be viewed as a symmetry-constrained information
  flow model.
- Split Clifford carriers can be viewed as rigid normal-form coordinates for
  transport.
- Non-commuting update order can be viewed as frustration/path dependence.

The phrase "D4 crystallography" belongs to this interpretation layer.

## 3. Empirical Bridge (what is required to physicalize)

To promote this from formal informational dynamics to a claim about reality,
an explicit calibration map is needed:

1. Observable map:
   - define which measured quantities correspond to interaction energy,
     temperature/inverse temperature, and transport cost.
2. Measurement protocol:
   - give procedures that reconstruct the mapped quantities from data.
3. Falsifiability:
   - specify which theorem-constrained inequalities/equalities must hold and
     what observation would violate them.

Consistency note:
- Hysteresis claims in this document should be tied to the exact witness theorems
  above (not to unrelated bounds).
- For current theorem-to-experiment extraction style, see
  `docs/testable_predictions.md`.
