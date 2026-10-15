import InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis

namespace InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis

/-!
# Kernel Axiom Audit for `KahlerDiracWeitzenbockSynthesis`

This audit companion prints the transitive kernel axiom dependencies of all
27 theorems in `KahlerDiracWeitzenbockSynthesis.lean` (`[propext, Classical.choice, Quot.sound]`,
with zero custom axioms or proof holes).
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
#print axioms weitzenbock_curvature_decomposition
#print axioms weitzenbock_scalar_curvature_apply
#print axioms kalbRamondContraction_symm
#print axioms kalbRamondContraction_diag_nonneg
#print axioms bismutDilatonRicciTensor_isSymm
#print axioms bismutDilatonRicciTensor_zero_flux

end InfoGeometry.Superalgebra.KahlerDiracWeitzenbockSynthesis
