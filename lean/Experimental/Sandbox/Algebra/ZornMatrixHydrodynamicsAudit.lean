import Experimental.Sandbox.Algebra.ZornMatrixHydrodynamics

open Experimental.Sandbox.Algebra.ZornMatrixHydrodynamics

/-!
# Axiomatic Audit for ZornMatrixHydrodynamics
Target: `lean/Experimental/Sandbox/Algebra/ZornMatrixHydrodynamicsAudit.lean`
-/

#print axioms dot3_comm
#print axioms dot3_pPlus_pMinus
#print axioms zornScalarMatrix_det
#print axioms zornKreinDet_exact
#print axioms zornKreinDet_eq_det_zornScalarMatrix
#print axioms zorn_energy_balance
#print axioms drazin_collapse_annihilates
#print axioms drazin_sink_idempotent
#print axioms drazin_projector_sum
#print axioms drazin_collapse_idempotent
#print axioms compile_zorn_matrix_hydrodynamics
