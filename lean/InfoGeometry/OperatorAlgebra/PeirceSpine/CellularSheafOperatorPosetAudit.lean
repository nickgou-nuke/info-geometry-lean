/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.MasterCausalPosetD1ToD15

/-!
# Axiom Audit for `CellularSheafOperatorPoset` and `MasterCausalPosetD1ToD15`

Prints the axiom dependencies of the listed stage, bridge, and audit declarations in
`CellularSheafOperatorPoset` and `MasterCausalPosetD1ToD15`. The build and output should be
read declaration-by-declaration; this companion does not assert a theorem about every
declaration in either owner file.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPosetAudit

open InfoGeometry.OperatorAlgebra.PeirceSpine

#print axioms CellularSheafStage.rank_injective
#print axioms CellularSheafStage.causalEdge_strict_rank_mono
#print axioms CellularSheafStage.causalEdge_irrefl
#print axioms mandelbrotTower_eq_idempotencyDefect_iterate
#print axioms sheafCoboundary0_eq_zero_of_aligned
#print axioms sheafCoboundary0_gauge_covariant
#print axioms star_sheafLaplacian0
#print axioms sheafLaplacian0_block_decomp
#print axioms sheafLaplacian0_block_decomp_and_self_adjoint
#print axioms sheafDirichletForm_eq_star_coboundary_mul
#print axioms sheafDirichlet_and_diffusion_equilibrium
#print axioms sheafLaplacian0_gauge_invariance
#print axioms sheafHodgeLaplacian_properties
#print axioms sheaf_to_tetraktys_bridge
#print axioms stage_D16_cellular_sheaf_operator_master_synthesis
#print axioms sheafLaplacian0_split_complex_block_separation
#print axioms sheafEdgeLaplacian1_structure_and_intertwining
#print axioms sheaf_horizon_normality_and_chiral_cross_coboundary
#print axioms sheafHodge_concrete_horizon_instantiation
#print axioms stage_D17_extended_cellular_sheaf_hodge_and_tetraktys_synthesis
#print axioms curved_sheaf_weitzenboeck_identity
#print axioms curved_sheaf_bianchi_identity
#print axioms sheafCoboundary0_swapped_cones_eq_zero
#print axioms mandelbrotTower_peirce_absorption
#print axioms defect_iterate_sheet_hodge_filtering
#print axioms fractal_sheet_hodge_filtering
#print axioms stage_D18_curved_sheaf_bianchi_and_fractal_hodge_cohomology
#print axioms multiEdgeSheafLaplacian_properties
#print axioms sheafDirichlet_positive_state_and_faithful_kernel
#print axioms curved_sheaf_energy_and_conditional_coercivity
#print axioms ArchetypeStage.rank_injective
#print axioms ArchetypeStage.causalEdge_strict_rank_mono
#print axioms ArchetypeStage.causalEdge_irrefl
#print axioms master_causal_poset_D1_to_D15
#print axioms selected_D15_D16_operator_synthesis
#print axioms selected_D15_to_D18_operator_synthesis

end InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPosetAudit
