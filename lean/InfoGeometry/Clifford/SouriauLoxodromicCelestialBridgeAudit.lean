import InfoGeometry.Clifford.SouriauLoxodromicCelestialBridge

/-!
# Audit File: SouriauLoxodromicCelestialBridgeAudit

This file audits the axiomatic footprint of `compile_souriau_loxodromic_celestial_bridge`
to ensure 0 sorry, 0 admit, and strictly standard foundational Lean 4 axioms.
-/

namespace InfoGeometry.Clifford.SouriauLoxodromicCelestial.Audit

open InfoGeometry.Clifford.SouriauLoxodromicCelestial

#print axioms boostRotor_unitary
#print axioms det2_Psi_boostRotor_unit
#print axioms boost_eigen_PPlus
#print axioms boost_eigen_PMinus
#print axioms boost_eigen_product
#print axioms rotRotor_unitary
#print axioms det2_Psi_rotRotor_unit
#print axioms det2_Psi_loxodromic_unit
#print axioms casimir_loxodromic_invariant
#print axioms celestial_null_casimir_preserved
#print axioms null_ray_forward_scaling
#print axioms log_scale_translation_additive
#print axioms souriau_sheet_casimir_conserved
#print axioms souriau_celestial_isoentropic
#print axioms compile_souriau_loxodromic_celestial_bridge

end InfoGeometry.Clifford.SouriauLoxodromicCelestial.Audit
