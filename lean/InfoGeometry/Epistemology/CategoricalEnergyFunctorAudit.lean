import InfoGeometry.Epistemology.CategoricalEnergyFunctor

/-!
# Audit File: Categorical Energy Stationarity & Poset Embedding

This module inspects the axiom readouts for the Categorical Energy Stationarity
and continuous-to-discrete certification bridge.
It verifies:
1. Zero `sorry`
2. Zero `admit`
3. Zero custom axioms
4. Standard Lean 4 core foundations: `[propext, Classical.choice, Quot.sound]`.
-/

namespace InfoGeometry.Epistemology.EnergyFunctor.Audit

open InfoGeometry.Epistemology.EnergyFunctor

#print axioms stationary_projector_annihilates_defect
#print axioms regular_projector_idempotent
#print axioms bregman_duality_projector_idempotent
#print axioms certified_state_invariant
#print axioms certification_respects_causal_order
#print axioms toCausalArchetypeOrderHom
#print axioms dyadic_energy_minima_is_vacuum_projector
#print axioms vacuum_state_zero_defect

/-- Smoke test verifying the monotonicity of the discrete embedding. -/
theorem audit_certification_order_verified :
    toCausalArchetype .uncertified ≤ toCausalArchetype .certified :=
  certification_respects_causal_order .uncertified .certified trivial

/-- Smoke test verifying the OrderHom preserves order. -/
theorem audit_order_hom_verified :
    toCausalArchetypeOrderHom .uncertified ≤ toCausalArchetypeOrderHom .certified :=
  toCausalArchetypeOrderHom.monotone trivial

end InfoGeometry.Epistemology.EnergyFunctor.Audit
