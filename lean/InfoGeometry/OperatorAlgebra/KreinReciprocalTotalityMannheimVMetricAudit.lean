/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric

/-!
# Axiom Audit for KreinReciprocalTotalityMannheimVMetric

Verifies via `#print axioms` that all declarations in
`InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric` depend solely on
Lean's permitted foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
-/

#print axioms InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric.reciprocalTotality_eq_reciprocityInvolution
#print axioms InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric.mannheimVMetric
#print axioms InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric.krein_reciprocalTotality_mannheim_V_metric
#print axioms InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric.mannheim_mat2Z_noncomm_exists
#print axioms InfoGeometry.OperatorAlgebra.KreinReciprocalTotalityMannheimVMetric.mat2Z_krein_ghost_and_mannheim_V_posdef_witness
