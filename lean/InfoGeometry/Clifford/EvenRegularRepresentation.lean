import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-!
# Continuous regular representation of the even Clifford algebra

`CliffordAlgebra.even Q` is Mathlib's native bundled associative algebra whose
underlying submodule is `CliffordAlgebra.evenOdd Q 0`.  On any finite-dimensional
normed realization of this algebra, left and right multiplication are therefore
continuous linear operators.

This file supplies the operator API needed by doubled/Schur constructions without
introducing a second even carrier or an additional algebra structure.
-/

noncomputable section

namespace InfoGeometry.Clifford.EvenRegularRepresentation

open CliffordAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M)

local notation "EvenQ" => CliffordAlgebra.even Q

/-- The native even-subalgebra carrier lies in the grade-zero `evenOdd` submodule. -/
theorem coe_mem_evenOdd_zero (a : EvenQ) :
    (a : CliffordAlgebra Q) ∈ CliffordAlgebra.evenOdd Q 0 := by
  simpa [CliffordAlgebra.even_toSubmodule] using a.2

/-- Algebraic left regular multiplication on the native even Clifford algebra. -/
def leftRegularLinearMap (a : EvenQ) : EvenQ →ₗ[ℝ] EvenQ :=
  LinearMap.mulLeft ℝ a

/-- Algebraic right regular multiplication on the native even Clifford algebra. -/
def rightRegularLinearMap (a : EvenQ) : EvenQ →ₗ[ℝ] EvenQ :=
  LinearMap.mulRight ℝ a

@[simp] theorem leftRegularLinearMap_apply (a x : EvenQ) :
    leftRegularLinearMap Q a x = a * x := by
  rfl

@[simp] theorem rightRegularLinearMap_apply (a x : EvenQ) :
    rightRegularLinearMap Q a x = x * a := by
  rfl

section Continuous

variable [NormedAddCommGroup EvenQ] [NormedSpace ℝ EvenQ]
variable [FiniteDimensional ℝ EvenQ]

/-- Finite-dimensional continuity of the left regular representation. -/
noncomputable def leftRegularContinuousLinearMap (a : EvenQ) : EvenQ →L[ℝ] EvenQ :=
  ContinuousLinearMap.mk (leftRegularLinearMap Q a)
    (LinearMap.continuous_of_finiteDimensional (leftRegularLinearMap Q a))

/-- Finite-dimensional continuity of the right regular representation. -/
noncomputable def rightRegularContinuousLinearMap (a : EvenQ) : EvenQ →L[ℝ] EvenQ :=
  ContinuousLinearMap.mk (rightRegularLinearMap Q a)
    (LinearMap.continuous_of_finiteDimensional (rightRegularLinearMap Q a))

@[simp] theorem leftRegularContinuousLinearMap_apply (a x : EvenQ) :
    leftRegularContinuousLinearMap Q a x = a * x := by
  rfl

@[simp] theorem rightRegularContinuousLinearMap_apply (a x : EvenQ) :
    rightRegularContinuousLinearMap Q a x = x * a := by
  rfl

/-- Left regular multiplication is a representation of multiplication by composition. -/
theorem leftRegularContinuousLinearMap_mul (a b : EvenQ) :
    leftRegularContinuousLinearMap Q (a * b) =
      (leftRegularContinuousLinearMap Q a).comp
        (leftRegularContinuousLinearMap Q b) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [mul_assoc]

/-- Right regular multiplication is the opposite representation under composition. -/
theorem rightRegularContinuousLinearMap_mul (a b : EvenQ) :
    rightRegularContinuousLinearMap Q (a * b) =
      (rightRegularContinuousLinearMap Q b).comp
        (rightRegularContinuousLinearMap Q a) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [mul_assoc]

/-- Left and right regular actions commute by associativity. -/
theorem leftRegularContinuousLinearMap_comp_rightRegularContinuousLinearMap
    (a b : EvenQ) :
    (leftRegularContinuousLinearMap Q a).comp
        (rightRegularContinuousLinearMap Q b) =
      (rightRegularContinuousLinearMap Q b).comp
        (leftRegularContinuousLinearMap Q a) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [mul_assoc]

@[simp] theorem leftRegularContinuousLinearMap_one :
    leftRegularContinuousLinearMap Q (1 : EvenQ) =
      ContinuousLinearMap.id ℝ EvenQ := by
  apply ContinuousLinearMap.ext
  intro x
  simp

@[simp] theorem rightRegularContinuousLinearMap_one :
    rightRegularContinuousLinearMap Q (1 : EvenQ) =
      ContinuousLinearMap.id ℝ EvenQ := by
  apply ContinuousLinearMap.ext
  intro x
  simp

/-- Left multiplication by a unit is a linear equivalence. -/
noncomputable def leftRegularLinearEquiv (u : EvenQˣ) : EvenQ ≃ₗ[ℝ] EvenQ where
  toLinearMap := leftRegularLinearMap Q (u : EvenQ)
  invFun := fun x => (↑(u⁻¹) : EvenQ) * x
  left_inv := by
    intro x
    simp [leftRegularLinearMap, mul_assoc]
  right_inv := by
    intro x
    simp [leftRegularLinearMap, mul_assoc]

/-- Right multiplication by a unit is a linear equivalence. -/
noncomputable def rightRegularLinearEquiv (u : EvenQˣ) : EvenQ ≃ₗ[ℝ] EvenQ where
  toLinearMap := rightRegularLinearMap Q (u : EvenQ)
  invFun := fun x => x * (↑(u⁻¹) : EvenQ)
  left_inv := by
    intro x
    simp [rightRegularLinearMap, mul_assoc]
  right_inv := by
    intro x
    simp [rightRegularLinearMap, mul_assoc]

/-- Left multiplication by a unit is a continuous linear equivalence. -/
noncomputable def leftRegularContinuousLinearEquiv (u : EvenQˣ) : EvenQ ≃L[ℝ] EvenQ :=
  (leftRegularLinearEquiv Q u).toContinuousLinearEquiv

/-- Right multiplication by a unit is a continuous linear equivalence. -/
noncomputable def rightRegularContinuousLinearEquiv (u : EvenQˣ) : EvenQ ≃L[ℝ] EvenQ :=
  (rightRegularLinearEquiv Q u).toContinuousLinearEquiv

@[simp] theorem leftRegularContinuousLinearEquiv_apply (u : EvenQˣ) (x : EvenQ) :
    leftRegularContinuousLinearEquiv Q u x = (u : EvenQ) * x := by
  rfl

@[simp] theorem rightRegularContinuousLinearEquiv_apply (u : EvenQˣ) (x : EvenQ) :
    rightRegularContinuousLinearEquiv Q u x = x * (u : EvenQ) := by
  rfl

/-- The continuous equivalence has the same underlying operator as left regular multiplication. -/
theorem leftRegularContinuousLinearEquiv_toContinuousLinearMap (u : EvenQˣ) :
    (leftRegularContinuousLinearEquiv Q u).toContinuousLinearMap =
      leftRegularContinuousLinearMap Q (u : EvenQ) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The continuous equivalence has the same underlying operator as right regular multiplication. -/
theorem rightRegularContinuousLinearEquiv_toContinuousLinearMap (u : EvenQˣ) :
    (rightRegularContinuousLinearEquiv Q u).toContinuousLinearMap =
      rightRegularContinuousLinearMap Q (u : EvenQ) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

end Continuous

end InfoGeometry.Clifford.EvenRegularRepresentation

end noncomputable section
