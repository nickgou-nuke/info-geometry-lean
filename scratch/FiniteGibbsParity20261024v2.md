# Finite Gibbs parity v2

Uncompiled; independent AA and locked QA pending. No builds/tests or live edits.
V1 retained unchanged. Generic four lemmas and imports unchanged from v1.

Concrete correction: H=h•tilt2, parity Γ=tilt2, observable X=switch2,
for every h,β : ℝ. These are the existing KleinBottleSewingExact matrices;
Γ is diagonal (1,-1), X is off-diagonal Pauli X. The reversed anticommutation
is derived from tilt2_switch2_anticomm. No copied carrier or matrix definition.
This matches the Klein naming convention, but does not claim a proved
LinearMap.toMatrix' transport equality with AnomalousKMSFlow operators.

Concrete heads: tiltHamiltonian_isHermitian, tiltHamiltonian_gibbs_switch_zero.
Other heads: gibbsDensity_commutes_of_commute, gibbsDensity_parity_invariant,
weightedTrace_gibbsDensity_odd_zero, gibbsFunctional_odd_zero.
Use v2 instead of v1, not alongside it: generic declaration names are retained.
No Γ-Hermitian hypothesis in the general result; no global weighted cyclicity
or DeltaRegularized assumption. Native CFC and trace cancellation are reused.
