# GNS vacuum covariance candidate contract

Status: G-A source proposal; uncompiled, independent A-A and QA pending.
Only the sibling Lean candidate and this contract are authored here.

Import: `InfoGeometry.Prequantum.GNSAction`.
Namespace: `InfoGeometry.Prequantum.GNSAction.RepresentationState`.

## Native owners and reuse

- `lean/InfoGeometry/Prequantum/GNSAction.lean`: existing `RepresentationState`,
  `pullback`, `act`, `vacuum`, `act_vacuum`, `gnsQuotientEquiv_intertwines`,
  and `gnsQuotientEquiv_vacuum`.
- `lean/InfoGeometry/Prequantum/AlgebraicGNSState.lean`: existing
  `RealAlgebraicState.statePullback`, `statePullback_gnsEquiv_iff`, and
  `gnsQuotientEquiv`. The second candidate lemma reuses the null-relation iff
  at `(a, 0)` rather than reconstructing quotient transport.
- `lean/InfoGeometry/Prequantum/GNSBridge.lean`: existing quotient setoid and
  `AbstractGNSState.gnsNullSet`.
- `lean/InfoGeometry/QuantumContext/AttentionGNSBridge.lean`:
  `vacuum_annihilator_iff_null` is the existing real-matrix specialization.
  The first candidate exposes the same fact for arbitrary native
  `RepresentationState A`, without importing the attention implementation.

## Exact delta

1. `act_vacuum_eq_zero_iff_null`: `S.act a S.vacuum = [0]` iff
   `a ∈ S.state.gnsNullSet`.
2. `pullback_act_vacuum_eq_zero_iff`: for a real algebra equivalence `e`
   with explicit star preservation `he`, the pulled-back state's action of
   `a` kills its vacuum iff the original state's action of `e a` kills its
   vacuum.

Both use `[Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]` and the
existing positive normalized real `RepresentationState`, including its
native null-left-ideal property. No new hypotheses assert either conclusion.
`[0]` is literally `Quotient.mk` for the appropriate native setoid, not a
new zero instance or a new quotient carrier.

## Direction and consumer boundary

The native pullback functional is `φ ∘ e`. For covariance written as
`ψ = φ ∘ α⁻¹`, instantiate `e = α.symm`; the native quotient equivalence
runs from the ψ quotient to the φ quotient. Its inverse gives the forward
map `[x]φ ↦ [α x]ψ`. Inner-unitary specialization can supply `α` through
mathlib `Unitary.conjStarAlgAut` and its star-preservation law; the candidate
does not add a separate inner-unitary wrapper.

These are cyclic-vacuum annihilator statements, not vanishing of the entire
represented operator. They make no completed complex GNS, Hilbert isometry,
KMS, analytic modular theory, or arbitrary weighted-functional positivity
claim. They do not identify different states without the explicit pullback.

Parent owns promotion and independent review/locked verification. No builds
or tests were run for this proposal; successful elaboration and axiom/warning
checks remain pending.
