/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridge

/-!
# Audit: `Frontier103CuntzLeptonQuarkUnruhKleinBridge`

External `#check` audit verifying exported theorem and definition signatures for
`InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridge`.
-/

namespace InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridgeAudit

open InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridge

#check @cl22_dirac_carrier_noncomm
#check @P_plus
#check @P_minus
#check @interSheetComplexJ
#check @supertrace22
#check @P_plus_explicit
#check @P_minus_explicit
#check @P_plus_add_P_minus_eq_one
#check @n_plus_1_mul_P_plus_eq_zero
#check @P_minus_mul_n_plus_1_eq_zero
#check @n_plus_1_peirce_absorption
#check @P_plus_P_minus_idempotent_orthogonal
#check @P_plus_P_minus_trace_and_interSheetComplexJ_supertrace
#check @cuntz_toeplitz_doubled_dirac_master_bridge
#check @beta_eq_inv_unruhTemperature
#check @unruh_gibbs_surprisal_first_law_bridge
#check @weylBoostMatrix
#check @weylBoostConjugate
#check @logConformalKKSTwoForm
#check @unruh_weyl_soldered_kks_master_bridge
#check @leptonSubspaceProj
#check @quarkSubspaceProj
#check @embedPureLepton
#check @embedPureQuark
#check @twistor55_lepton_quark_direct_sum_decomposition
#check @splitOctonionQuadraticForm
#check @lepton_sector_klein_quadric_reduction
#check @zornNorm_lepton_sector_reduction

end InfoGeometry.Synthesis.Frontier103CuntzLeptonQuarkUnruhKleinBridgeAudit
