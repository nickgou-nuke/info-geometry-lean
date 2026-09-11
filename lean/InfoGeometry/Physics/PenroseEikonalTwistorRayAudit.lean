import InfoGeometry.Physics.PenroseEikonalTwistorRay

/-!
# Axiom Audit: Penrose Eikonal Twistor Ray Information Geometry

Audits all theorems to ensure 0 debt, 0 custom axioms, and dependency strictly
on standard Lean 4 axioms: `[propext, Classical.choice, Quot.sound]`.
-/

open InfoGeometry.Physics.PenroseEikonalTwistorRay

#print axioms det_pauliSoldering_eq_minkowskiNorm
#print axioms null_iff_det_pauliSoldering_zero
#print axioms det_weylDyad_zero
#print axioms spinor_generates_null_vector
#print axioms spinor_energy_nonneg
#print axioms incident_twistor_is_null
#print axioms sachs_trace_expansion
#print axioms eikonal_vorticity_annihilation
#print axioms sachs_ray_focusing
#print axioms information_flux_conservation
#print axioms conformal_null_invariance
#print axioms certified_penrose_eikonal_twistor_synthesis
