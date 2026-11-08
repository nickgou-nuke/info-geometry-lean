/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.PositiveZeroColumnDeformation

open InfoGeometry.Canonical InfoGeometry.Topology Matrix

#print axioms hasPositiveMaximalMinors_iff_columnMinor₂
#print axioms appendPositiveColumn₂_zero
#print axioms columnMinor₂_appendPositive_last
#print axioms appendPositiveColumn₂_positive
#print axioms continuous_appendPositiveColumn₂
#print axioms appendZeroColumn₂_mem_closure_positive
#print axioms appendZeroColumn₂_mem_frontier_positive
#print axioms appendZeroColumn₂_not_mem_positiveGrassmannianInterior

private theorem identity_positive :
    HasPositiveMaximalMinors (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [hasPositiveMaximalMinors_iff_columnMinor₂]
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [columnMinor₂, Matrix.one_apply] at *

example : appendZeroColumn₂ (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈
    frontier (positiveGrassmannianInterior (k := 2) (n := 3)) :=
  appendZeroColumn₂_mem_frontier_positive _ identity_positive

example : HasPositiveMaximalMinors
    (appendPositiveColumn₂ (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2)) :=
  appendPositiveColumn₂_positive _ identity_positive (by norm_num)

example : appendPositiveColumn₂ (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 =
    !![1, 0, -1; 0, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [appendPositiveColumn₂, Matrix.one_apply, Fin.last]
