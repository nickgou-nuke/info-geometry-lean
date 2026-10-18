/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis

/-!
# Audit: `Z2Z2KoszulOperadicHomologyShirokovSynthesis`

External `#check` and `#print axioms` audit for Frontier 104 (Wave 8):
`InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis`.
-/

namespace InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesisAudit

open InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesis

#check @koszul_cl11_mat2_noncomm
#check @koszul_peirce_mat3_noncomm
#check @koszulDualGrade
#check @koszulDualGrade_invariance_and_duality
#check @z2z2MatrixBracket
#check @z2z2_koszul_operadic_bracket_and_differential_laws
#check @homological_context_supertrace_invariance
#check @shirokovSuperBerezinian23
#check @cl11ShirokovTrace_smul_one
#check @shirokov_matrix_free_superBerezinian_horizon_synthesis

#print axioms koszul_cl11_mat2_noncomm
#print axioms koszul_peirce_mat3_noncomm
#print axioms koszulDualGrade_invariance_and_duality
#print axioms z2z2_koszul_operadic_bracket_and_differential_laws
#print axioms homological_context_supertrace_invariance
#print axioms cl11ShirokovTrace_smul_one
#print axioms shirokov_matrix_free_superBerezinian_horizon_synthesis

end InfoGeometry.Synthesis.Z2Z2KoszulOperadicHomologyShirokovSynthesisAudit

