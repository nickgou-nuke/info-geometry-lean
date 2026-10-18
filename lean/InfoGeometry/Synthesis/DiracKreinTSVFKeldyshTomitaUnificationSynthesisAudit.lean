/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Synthesis.DiracKreinTSVFKeldyshTomitaUnificationSynthesis

/-!
# Audit: `DiracKreinTSVFKeldyshTomitaUnificationSynthesis`

External `#check` and `#print axioms` audit for Frontier 105 (Wave 9):
`InfoGeometry.Synthesis.DiracKreinTSVFKeldyshTomitaUnificationSynthesis`.
-/

namespace InfoGeometry.Synthesis.DiracKreinTSVFKeldyshTomitaUnificationSynthesisAudit

open InfoGeometry.Synthesis.DiracKreinTSVFKeldyshTomitaUnificationSynthesis

#check @dirac_mat2_noncomm
#check @dirac_mat4_noncomm
#check @diracGamma0Krein4
#check @paraKahlerMetricMatrix4
#check @cayleyHadamardSheetTransform4
#check @diracKreinPairing4
#check @paraKahlerPairing4
#check @diracKreinAdjoint4
#check @dirac_conjugation_is_exact_krein_adjoint_and_paraKahler_congruent
#check @tsvfWeakValue
#check @tsvfProjector00
#check @tsvf_weakValue_calculus_and_anomalous_krein_witness
#check @schwingerKeldyshContourPairing
#check @keldyshParaKahlerPairing
#check @keldyshRotation
#check @schwingerKeldysh_tfd_paraKahler_equivalence
#check @tomitaSheetSwapConj
#check @leftCausalAction
#check @rightCommutantAction
#check @tomita_takesaki_sheet_swap_commutant_duality

#print axioms dirac_mat2_noncomm
#print axioms dirac_mat4_noncomm
#print axioms dirac_conjugation_is_exact_krein_adjoint_and_paraKahler_congruent
#print axioms tsvf_weakValue_calculus_and_anomalous_krein_witness
#print axioms schwingerKeldysh_tfd_paraKahler_equivalence
#print axioms tomita_takesaki_sheet_swap_commutant_duality

end InfoGeometry.Synthesis.DiracKreinTSVFKeldyshTomitaUnificationSynthesisAudit
