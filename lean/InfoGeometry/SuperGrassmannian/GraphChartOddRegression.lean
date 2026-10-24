/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.FreeSupermoduleChart
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Odd graph points invisible under augmentation

Over the actual exterior algebra on one generator, the graphs of `θ` and zero
are distinct points of the `1|0` graph chart in `1|1`, but have the same image
after killing the exterior generator. The odd basis parity of the second
summand is built into the native free-module grading. Valid even in characteristic
two: strict square-zero and nonzero-generator results do not cancel two.
-/

namespace InfoGeometry.SuperGrassmannian.GraphChartOddRegression

open GradedGraphChart GraphChartBaseChange FreeSupermoduleChart

variable (k : Type*) [CommRing k]

/-- Genuine exterior coefficients, not a newly postulated square-zero carrier. -/
abbrev Coeff := ExteriorAlgebra k k

/-- Native parity grading of the exterior algebra (`CliffordAlgebra 0`). -/
abbrev coeffGrade := CliffordAlgebra.evenOdd (0 : QuadraticForm k k)

noncomputable def theta : Coeff k := ExteriorAlgebra.ι k (1 : k)

theorem theta_odd : theta k ∈ coeffGrade k 1 :=
  CliffordAlgebra.ι_mem_evenOdd_one _ _

theorem theta_sq_zero : theta k * theta k = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem theta_ne_zero [Nontrivial k] : theta k ≠ 0 := by
  intro h
  exact one_ne_zero ((ExteriorAlgebra.ι_eq_zero_iff (R := k) (1 : k)).mp h)

/-- The graph of the odd coefficient `θ` is an even map from `A` to `ΠA`. -/
noncomputable def oddPoint :
    Chart (A := Coeff k) (freeGrade (coeffGrade k) (fun _ : Fin 1 => 0))
      (freeGrade (coeffGrade k) (fun _ : Fin 1 => 1)) :=
  coefficientChartEquiv (coeffGrade k) _ _
    ⟨fun _ _ => theta k, fun _ _ => by simpa using theta_odd k⟩

/-- The zero graph has the same fixed complement and rank as the odd graph. -/
noncomputable def zeroPoint :
    Chart (A := Coeff k) (freeGrade (coeffGrade k) (fun _ : Fin 1 => 0))
      (freeGrade (coeffGrade k) (fun _ : Fin 1 => 1)) :=
  coefficientChartEquiv (coeffGrade k) _ _
    ⟨fun _ _ => 0, fun _ _ => Submodule.zero_mem _⟩

/-- Odd coefficients really change the submodule, not just a chosen projector. -/
theorem oddPoint_ne_zeroPoint [Nontrivial k] : oddPoint k ≠ zeroPoint k := by
  intro h
  have hg := congrArg Subtype.val h
  simp only [oddPoint, zeroPoint, coefficientChartEquiv_submodule] at hg
  have hf := graph_injective hg
  have hx := congrFun (LinearMap.congr_fun hf (fun _ => 1)) (0 : Fin 1)
  apply theta_ne_zero k
  simpa using hx

/-- The augmentation kills the generator by the native exterior universal property. -/
@[simp] theorem augmentation_theta :
    (ExteriorAlgebra.algebraMapInv : Coeff k →ₐ[k] k) (theta k) = 0 := by
  simp [theta, ExteriorAlgebra.algebraMapInv]

/-- Both distinct chart points reduce to exactly the same graph submodule. -/
theorem same_reduction :
    extend (ExteriorAlgebra.algebraMapInv : Coeff k →ₐ[k] k).toRingHom (oddPoint k).val =
      extend (ExteriorAlgebra.algebraMapInv : Coeff k →ₐ[k] k).toRingHom (zeroPoint k).val := by
  simp only [oddPoint, zeroPoint, coefficientChartEquiv_submodule, extend_graph]
  simp

/-- Reduction fails to detect odd points, on the actual homogeneous-submodule chart. -/
theorem reduction_not_injective [Nontrivial k] :
    ¬ Function.Injective (fun S :
      Chart (A := Coeff k) (freeGrade (coeffGrade k) (fun _ : Fin 1 => 0))
        (freeGrade (coeffGrade k) (fun _ : Fin 1 => 1)) =>
      extend (ExteriorAlgebra.algebraMapInv : Coeff k →ₐ[k] k).toRingHom S.val) := by
  intro h
  exact oddPoint_ne_zeroPoint k (h (same_reduction k))

end InfoGeometry.SuperGrassmannian.GraphChartOddRegression
