/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Algebra.Zorn.FirstQuantizedLeftRegular

open InfoGeometry.Algebra

abbrev Carrier := ZornVectorMatrix ℝ

/-- The left-regular operator on the additive Zorn carrier. -/
def leftMul (x : Carrier) : Carrier →ₗ[ℝ] Carrier where
  toFun := fun z => ZornVectorMatrix.mul x z
  map_add' := by
    intro y z
    exact ZornVectorMatrix.mul_add x y z
  map_smul' := by
    intro r z
    exact ZornVectorMatrix.mul_smul r x z

@[simp] theorem leftMul_apply (x z : Carrier) :
    leftMul x z = ZornVectorMatrix.mul x z := rfl

/-- The defect of composing left multiplications with the product operator. -/
def leftMulDefect (x y : Carrier) : Carrier →ₗ[ℝ] Carrier :=
  (leftMul x).comp (leftMul y) - leftMul (ZornVectorMatrix.mul x y)

/-- The associator defect is retained explicitly by the operator lift. -/
theorem leftMul_comp_defect_eq_associator (x y z : Carrier) :
    leftMulDefect x y z =
      ZornVectorMatrix.mul x (ZornVectorMatrix.mul y z) -
        ZornVectorMatrix.mul (ZornVectorMatrix.mul x y) z := by
  rfl

/-- Left multiplication by an idempotent is an idempotent operator. -/
theorem leftMul_idempotent_of_idempotent
    {x : Carrier} (hx : ZornVectorMatrix.mul x x = x) :
    (leftMul x).comp (leftMul x) = leftMul x := by
  apply LinearMap.ext
  intro z
  have ha := ZornVectorMatrix.associator_left_alternative x z
  dsimp [ZornVectorMatrix.associator] at ha
  have heq : ZornVectorMatrix.mul (ZornVectorMatrix.mul x x) z =
      ZornVectorMatrix.mul x (ZornVectorMatrix.mul x z) := sub_eq_zero.mp ha
  change leftMul x (leftMul x z) = leftMul x z
  simp only [leftMul_apply]
  rw [← heq, hx]

/-- Square-zero multiplication gives a genuinely square-zero left operator. -/
theorem leftMul_squareZero_of_squareZero
    {x : Carrier} (hx : ZornVectorMatrix.mul x x = 0) :
    (leftMul x).comp (leftMul x) = 0 := by
  apply LinearMap.ext
  intro z
  have ha := ZornVectorMatrix.associator_left_alternative x z
  dsimp [ZornVectorMatrix.associator] at ha
  have heq : ZornVectorMatrix.mul (ZornVectorMatrix.mul x x) z =
      ZornVectorMatrix.mul x (ZornVectorMatrix.mul x z) := sub_eq_zero.mp ha
  change leftMul x (leftMul x z) = 0
  simp only [leftMul_apply]
  rw [← heq, hx]
  exact ZornVectorMatrix.zero_mul z

end InfoGeometry.Algebra.Zorn.FirstQuantizedLeftRegular
