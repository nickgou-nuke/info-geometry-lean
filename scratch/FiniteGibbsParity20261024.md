# Finite Gibbs parity cancellation

Uncompiled scratch candidate. Independent AA and locked QA required; no builds,
tests, CAS, or live-owner edits performed.

Native owners reused:
- Canonical.FiniteMatrixGibbsFunctional: actual CFC exponential density,
  positivity, nonzero partition, normalized positive functional.
- Mathlib Commute.cfc_real: commutation with real continuous functional calculus.
- Physics.KleinBottleSewingExact.trace_mul_eq_zero_of_anticomm_invariance:
  trace cancellation for an invariant density and odd observable.
- Existing switch2/tilt2 matrices, switch2_sq, tilt2_switch2_anticomm.

Bounded search found Gibbs stationarity for H itself, but no matching arbitrary
commuting parity Gibbs cancellation. ChiralParityGibbsDeformation is a scalar
weight owner, not this finite matrix assertion.

Hypotheses: H Hermitian; Commute H Γ; Γ²=1; XΓ=-(ΓX); β arbitrary real.
Γ need not be Hermitian, unitary, or supplied with a star hypothesis. The first
CFC commutation lemma does not even require Γ²=1. Nonempty index is needed only
for the native normalized functional. No global weighted cyclicity, global
DeltaRegularized defect vanishing, or analytic strip condition is assumed.

Six theorem heads: gibbsDensity_commutes_of_commute,
gibbsDensity_parity_invariant, weightedTrace_gibbsDensity_odd_zero,
gibbsFunctional_odd_zero, switchHamiltonian_isHermitian,
switchHamiltonian_gibbs_tilt_zero. The last uses H=h•switch2, Γ=switch2,
X=tilt2 on the native Fin 2 complex matrix carrier, for every real h and β.
No copied matrix definition, new carrier, or witness package is introduced.
