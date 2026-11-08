/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.SolderingIsotropicSouriauSheetBridge

/-!
# Audit File: SolderingIsotropicSouriauSheetBridgeAudit

This file audits the axiomatic footprint of the genuine owner lemmas in
`SolderingIsotropicSouriauSheetBridge`.
to ensure 0 sorry, 0 admit, and strictly standard foundational Lean 4 axioms.
-/

namespace InfoGeometry.Clifford.SolderingIsotropic.Audit

open InfoGeometry.Clifford.SolderingIsotropic

#print axioms det2_solderingMatrix
#print axioms det2_transpose
#print axioms det2_two_sided_conjugation
#print axioms lorentz_invariance_minkowski
#print axioms soldering_lorentz_invariant
#print axioms P_L_sq
#print axioms P_R_sq
#print axioms P_L_mul_P_R
#print axioms P_R_mul_P_L
#print axioms P_L_add_P_R
#print axioms det2_P_L
#print axioms det2_P_R
#print axioms det2_spinorDyad
#print axioms souriau_sheet_L_isotropic
#print axioms souriau_sheet_R_isotropic
#print axioms souriau_chiral_sum_unimodular
end InfoGeometry.Clifford.SolderingIsotropic.Audit
