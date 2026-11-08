/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge

/-!
# Audit: `WavefrontKMSKleinDualityBridge`

External `#check` and `#print axioms` audit verifying exported theorem and definition signatures
for `InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge`.
-/

namespace InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridgeAudit

open InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridge

#check @colorGenE01
#check @colorGenE10
#check @colorGen_mul_ne_comm
#check @zornProjLeptonA
#check @zornProjLeptonB
#check @zornProjQuark
#check @zornProjAntiQuark
#check @zorn_gunaydin_gursey_direct_sum_decomposition
#check @zorn_quark_color_ray_norm_zero
#check @zornColorSingletPairing
#check @zornNorm_eq_lepton_sub_colorSingletPairing
#check @sedenionOppositeWeylScale
#check @sedenionG2Derivation_commutes_oppositeWeylScale
#check @realPeirce_color_weyl_fock_spine
#check @hadjiivanov_cyclotomic_w24_monodromy_spine
#check @wavefront_kms_klein_duality_master_spine
#check @celestialQuarkCoord
#check @celestialAntiQuarkCoord
#check @celestial_null_quadric_and_doubleStar_root_sheet_spine

#print axioms colorGen_mul_ne_comm
#print axioms zorn_gunaydin_gursey_direct_sum_decomposition
#print axioms zorn_quark_color_ray_norm_zero
#print axioms zornNorm_eq_lepton_sub_colorSingletPairing
#print axioms sedenionG2Derivation_commutes_oppositeWeylScale
#print axioms realPeirce_color_weyl_fock_spine
#print axioms hadjiivanov_cyclotomic_w24_monodromy_spine
#print axioms wavefront_kms_klein_duality_master_spine
#print axioms celestial_null_quadric_and_doubleStar_root_sheet_spine

end InfoGeometry.Synthesis.WavefrontKMSKleinDualityBridgeAudit
