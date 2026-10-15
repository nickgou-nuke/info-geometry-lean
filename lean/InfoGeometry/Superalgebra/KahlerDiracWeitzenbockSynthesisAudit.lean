import InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis

namespace InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis

/-!
# Kernel Axiom Audit for `KahlerDiracWeitzenbockSynthesis`

This companion prints transitive kernel axiom dependencies. It audits kernel
dependencies only; it does not certify that theorem names or prose match a
broader geometric interpretation.
-/

#print axioms exteriorWedge_apply
#print axioms exteriorContract_one
#print axioms exteriorWedge_sq
#print axioms exteriorContract_sq
#print axioms exteriorWedge_anticomm
#print axioms exteriorContract_anticomm
#print axioms exteriorContract_wedge_apply
#print axioms exteriorContract_iota
#print axioms exterior_cartan_homotopy_car
#print axioms exteriorContract_wedge_noncommute_witness
#print axioms chevalleyAction_one
#print axioms chevalleyAction_iota
#print axioms chevalleyAction_sq
#print axioms chevalleyAction_anticomm
#print axioms kahlerDirac_sq_expansion
#print axioms kahlerDirac_sq_eq_hodgeLaplacian
#print axioms cliffordDiracSub_sq_eq_neg_hodgeLaplacian
#print axioms hodgeLaplacian_comm_d
#print axioms hodgeLaplacian_comm_delta
#print axioms kahlerDirac_comm_hodgeLaplacian
#print axioms kahlerDirac_harmonic_imp_hodge_harmonic
#print axioms diracOperator₂_sq_weitzenbock
#print axioms dirac_sq_remainder_decomposition
#print axioms dirac_sq_scalar_remainder_apply
#print axioms finiteQuadraticTensorContraction_symm
#print axioms finiteQuadraticTensorContraction_diag_nonneg
#print axioms weightedRicciHessianTensor_isSymm
#print axioms weightedRicciHessianTensor_zero_corrections

end InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
