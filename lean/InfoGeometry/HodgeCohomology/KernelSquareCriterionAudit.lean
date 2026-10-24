/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.HodgeCohomology.KernelSquareCriterion
import InfoGeometry.HodgeCohomology.KreinHodgeObstruction
open InfoGeometry.HodgeCohomology
open KreinHodgeObstruction
#print axioms kernel_square_eq_iff
#print axioms square_zero_kernel_stable_iff
#print axioms nullDirac_kernel_counterexample

example : ¬ Disjoint (LinearMap.range nullDirac.toLinearMap)
    (LinearMap.ker nullDirac.toLinearMap) := by
  intro h
  apply nullDirac_kernel_counterexample
  exact (kernel_square_eq_iff nullDirac.toLinearMap).mpr h
