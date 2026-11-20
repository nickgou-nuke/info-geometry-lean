/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SolveEtCoagulaAlignmentAndKurkaParabolic

/-!
# Axiom Audit for SolveEtCoagulaAlignmentAndKurkaParabolic

Verifies via `#print axioms` that all exported theorems in
`InfoGeometry.Canonical.SolveEtCoagulaAlignmentAndKurkaParabolic` depend exclusively
on Lean 4's foundational axioms (`propext`, `Quot.sound`, `Classical.choice`),
with zero `sorry`, `admit`, `native_decide`, or custom axioms.
-/

open InfoGeometry.Canonical.SolveEtCoagulaAlignmentAndKurkaParabolic

#print axioms matrixE01_mul_E10_ne_mul_E10_E01
#print axioms solveEtCoagulaEdge_iff_coagulaCovers
#print axioms solveEtCoagulaEdge_iff_aporiaCover
#print axioms solveEtCoagulaReach_iff_coagulaTransGen
#print axioms solveEtCoagulaReach_iff_aporiaTransGen
#print axioms epistemic_eq_indefiniteReciprocalTotality_suite
#print axioms kurkaParabolicMap_eq_sub_square
#print axioms kurkaParabolicMat_trace
#print axioms kurkaParabolicMat_det
#print axioms kurkaParabolicMap_eq_matrixAction
#print axioms kurkaParabolicMat_det_ne_zero
#print axioms kurkaParabolicMat_sub_scalar_sq
#print axioms kurkaParabolicMat_sub_scalar_ne_zero
#print axioms kurkaParabolicMap_fixed_point
#print axioms kurkaParabolicMap_hasDerivAt
#print axioms kurkaParabolicMap_second_deriv
#print axioms bugTurn41_refutation
#print axioms bugSourceA_deriv_refutation
#print axioms jordanBlock2_not_diagonalizable
#print axioms jungianArchetype_to_aporiaCoagulaNode_strictMono
