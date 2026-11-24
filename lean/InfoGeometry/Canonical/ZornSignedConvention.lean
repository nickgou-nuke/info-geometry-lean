/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCliffordRepresentation
import InfoGeometry.Canonical.ZornMultiplicationOperators
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# Transport of the opposite cross-product convention

The input convention has upper `+cross` and lower `-cross`. The canonical
owner has upper `-cross` and lower `+cross`. Negating both vector coordinates
transports the complete product. All operators below remain on the existing
real canonical carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornSignedConvention

open ZornMatrix ZornClifford

-- Normalize finite-vector projections introduced by Zorn multiplication.
attribute [local simp] Matrix.vecHead Matrix.vecTail

/-- Coordinates for the input cross orientation, transported to the canonical
Zorn carrier. This is a linear equivalence, not an algebra automorphism of
the canonical multiplication. -/
def signedCoordinates : ZornMatrix.Coord ℝ ≃ₗ[ℝ] ZornMatrix ℝ where
  toFun z := ⟨z.1, z.2.1, -z.2.2.1, -z.2.2.2⟩
  invFun z := (z.a, z.b, -z.x, -z.y)
  left_inv z := by
    rcases z with ⟨a, b, x, y⟩
    simp
  right_inv z := by
    apply ZornMatrix.ext <;> simp
  map_add' z w := by
    apply ZornMatrix.ext <;> simp [add_comm]
  map_smul' r z := by
    apply ZornMatrix.ext <;> simp

/-- Exact multiplication compatibility, including both cross-product terms. -/
theorem signedCoordinates_mul (a b c d : ℝ) (x y u v : Fin 3 → ℝ) :
    signedCoordinates (a, b, x, y) * signedCoordinates (c, d, u, v) =
      signedCoordinates
        (a * c + dot x v, b * d + dot u y,
          a • u + d • x + cross y v, c • y + b • v - cross x u) := by
  apply ZornMatrix.ext
  · simp [signedCoordinates, ZornMatrix.mul, dot]
  · simp [signedCoordinates, ZornMatrix.mul, dot]
    ring
  · funext i
    fin_cases i <;> simp [signedCoordinates, ZornMatrix.mul, cross] <;> ring
  · funext i
    fin_cases i <;> simp [signedCoordinates, ZornMatrix.mul, cross] <;> ring

theorem signedCoordinates_norm (a b : ℝ) (x y : Fin 3 → ℝ) :
    zornNorm (signedCoordinates (a, b, x, y)) = a * b - dot x y := by
  simp [zornNorm_apply, zornNormFun, signedCoordinates, dot]

/-- The input upper four-vector in the canonical orientation. -/
def primal (x : Fin 4 → ℝ) : ZornMatrix ℝ :=
  signedCoordinates (x 0, 0, ![x 1, x 2, x 3], 0)

/-- The input lower four-vector in the canonical orientation. -/
def dual (p : Fin 4 → ℝ) : ZornMatrix ℝ :=
  signedCoordinates (0, p 0, 0, ![p 1, p 2, p 3])

/-- The temporal lower coefficient contributes an upper vector term. -/
theorem primal_mul_dual (x p : Fin 4 → ℝ) :
    primal x * dual p =
      signedCoordinates
        (x 1 * p 1 + x 2 * p 2 + x 3 * p 3, 0,
          p 0 • ![x 1, x 2, x 3], 0) := by
  rw [primal, dual, signedCoordinates_mul]
  congr 1
  simp [dot, cross]

/-- Reversing the factors changes both the diagonal and vector channels. -/
theorem dual_mul_primal (x p : Fin 4 → ℝ) :
    dual p * primal x =
      signedCoordinates
        (0, x 1 * p 1 + x 2 * p 2 + x 3 * p 3,
          0, x 0 • ![p 1, p 2, p 3]) := by
  rw [dual, primal, signedCoordinates_mul]
  congr 1
  simp [dot, cross]

/-- The primal-dual contraction is the norm of their sum. -/
theorem primal_add_dual_norm (x p : Fin 4 → ℝ) :
    zornNorm (primal x + dual p) =
      x 0 * p 0 - x 1 * p 1 - x 2 * p 2 - x 3 * p 3 := by
  simp [primal, dual, signedCoordinates, zornNorm_apply, zornNormFun, dot]
  ring

/-- The input quaternion axis is lower minus upper in canonical coordinates. -/
def quaternionAxis (i : Fin 3) : ZornMatrix ℝ :=
  chiralLowerBasis i - chiralUpperBasis i

/-- The input split axis is the negative of both canonical vector slots. -/
def splitAxis (i : Fin 3) : ZornMatrix ℝ :=
  -chiralUpperBasis i - chiralLowerBasis i

/-- The diagonal split unit. -/
def splitUnit : ZornMatrix ℝ := zornPlus - zornMinus

theorem signed_upper_mul_upper :
    (-chiralUpperBasis (R := ℝ) 0) * (-chiralUpperBasis 1) =
      chiralLowerBasis 2 := by
  apply ZornMatrix.ext
  · simp [ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, dot]
  · simp [ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, dot]
  · funext i; fin_cases i <;>
      simp [ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, cross]
  · funext i; fin_cases i <;>
      simp [ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, cross]

theorem signed_lower_mul_lower :
    chiralLowerBasis (R := ℝ) 0 * chiralLowerBasis 1 =
      -chiralUpperBasis 2 := by
  apply ZornMatrix.ext
  · simp [ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, dot]
  · simp [ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, dot]
  · funext i; fin_cases i <;>
      simp [ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, cross]
  · funext i; fin_cases i <;>
      simp [ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, cross]

theorem quaternionAxis_sq (i : Fin 3) :
    quaternionAxis i * quaternionAxis i = -1 := by
  fin_cases i <;> apply ZornMatrix.ext
  all_goals first
    | (funext j; fin_cases j <;>
        simp [quaternionAxis, ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis,
          dot, cross])
    | simp [quaternionAxis, ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis,
        dot, cross]

theorem quaternionAxis_zero_mul_one :
    quaternionAxis 0 * quaternionAxis 1 = quaternionAxis 2 := by
  apply ZornMatrix.ext
  all_goals first
    | (funext j; fin_cases j <;>
        simp [quaternionAxis, ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis,
          dot, cross])
    | simp [quaternionAxis, ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis,
        dot, cross]

theorem splitUnit_mul_quaternionAxis (i : Fin 3) :
    splitUnit * quaternionAxis i = splitAxis i := by
  apply ZornMatrix.ext
  all_goals first
    | (funext j; fin_cases i <;> fin_cases j <;>
        simp [splitUnit, splitAxis, quaternionAxis, zornPlus, zornMinus,
          ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, dot, cross])
    | simp [splitUnit, splitAxis, quaternionAxis, zornPlus, zornMinus,
        ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, dot, cross]

/-- The diagonal split unit squares to the octonion identity. -/
theorem splitUnit_sq : splitUnit * splitUnit = 1 := by
  change rightMulLinear (zornPlus - zornMinus) (zornPlus - zornMinus) = 1
  simp only [map_sub]
  change leftMulLinear zornPlus (zornPlus - zornMinus) -
    leftMulLinear zornMinus (zornPlus - zornMinus) = 1
  simp only [map_sub]
  change (zornPlus * zornPlus - zornPlus * zornMinus) -
    (zornMinus * zornPlus - zornMinus * zornMinus) = (1 : ZornMatrix ℝ)
  rw [zornPlus_idempotent, zornPlus_mul_zornMinus,
    zornMinus_mul_zornPlus, zornMinus_idempotent]
  simpa only [sub_zero, zero_sub, sub_neg_eq_add] using
    (zornPlus_add_zornMinus (R := ℝ))

/-- The three signed split axes have positive octonion square. -/
theorem splitAxis_sq (i : Fin 3) : splitAxis i * splitAxis i = 1 := by
  fin_cases i <;> apply ZornMatrix.ext
  all_goals first
    | (funext j; fin_cases j <;>
        simp [splitAxis, ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis,
          dot, cross])
    | simp [splitAxis, ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis,
        dot, cross]

/-- Right multiplication by the split unit has the opposite sign to its
existing left action on a quaternion axis. -/
theorem quaternionAxis_mul_splitUnit (i : Fin 3) :
    quaternionAxis i * splitUnit = -splitAxis i := by
  apply ZornMatrix.ext
  all_goals first
    | (funext j; fin_cases i <;> fin_cases j <;>
        simp [splitUnit, splitAxis, quaternionAxis, zornPlus, zornMinus,
          ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, dot, cross])
    | simp [splitUnit, splitAxis, quaternionAxis, zornPlus, zornMinus,
        ZornMatrix.mul, chiralUpperBasis, chiralLowerBasis, dot, cross]

/-- Recover the signed upper ladder from the quaternion and split axes. -/
theorem signed_upper_eq_half_axes (i : Fin 3) :
    -chiralUpperBasis (R := ℝ) i =
      (1 / 2 : ℝ) • (quaternionAxis i + splitAxis i) := by
  have hsum : quaternionAxis i + splitAxis i =
      (2 : ℝ) • (-chiralUpperBasis (R := ℝ) i) := by
    simp only [quaternionAxis, splitAxis, two_smul]
    abel
  rw [hsum, one_div, inv_smul_smul₀ (two_ne_zero : (2 : ℝ) ≠ 0)]

/-- Recover the signed lower ladder from the quaternion and split axes. -/
theorem signed_lower_eq_half_axes (i : Fin 3) :
    chiralLowerBasis (R := ℝ) i =
      (1 / 2 : ℝ) • (quaternionAxis i - splitAxis i) := by
  have hdiff : quaternionAxis i - splitAxis i =
      (2 : ℝ) • chiralLowerBasis (R := ℝ) i := by
    simp only [quaternionAxis, splitAxis, two_smul]
    abel
  rw [hdiff, one_div, inv_smul_smul₀ (two_ne_zero : (2 : ℝ) ≠ 0)]

/-- Recover the upper temporal idempotent from the unit and split unit. -/
theorem zornPlus_eq_half_one_add_splitUnit :
    zornPlus (R := ℝ) = (1 / 2 : ℝ) • (1 + splitUnit) := by
  have hsum : (1 : ZornMatrix ℝ) + splitUnit =
      (2 : ℝ) • zornPlus (R := ℝ) := by
    rw [← zornPlus_add_zornMinus (R := ℝ)]
    simp only [splitUnit, two_smul]
    abel
  rw [hsum, one_div, inv_smul_smul₀ (two_ne_zero : (2 : ℝ) ≠ 0)]

/-- Recover the lower temporal idempotent from the unit and split unit. -/
theorem zornMinus_eq_half_one_sub_splitUnit :
    zornMinus (R := ℝ) = (1 / 2 : ℝ) • (1 - splitUnit) := by
  have hdiff : (1 : ZornMatrix ℝ) - splitUnit =
      (2 : ℝ) • zornMinus (R := ℝ) := by
    rw [← zornPlus_add_zornMinus (R := ℝ)]
    simp only [splitUnit, two_smul]
    abel
  rw [hdiff, one_div, inv_smul_smul₀ (two_ne_zero : (2 : ℝ) ≠ 0)]


theorem norm_one : zornNorm (1 : ZornMatrix ℝ) = 1 := by
  simp [zornNorm_apply, zornNormFun, dot]

theorem norm_quaternionAxis (i : Fin 3) : zornNorm (quaternionAxis i) = 1 := by
  fin_cases i <;>
    simp [quaternionAxis, chiralUpperBasis, chiralLowerBasis, zornNorm_apply,
      zornNormFun, dot]

theorem norm_splitUnit : zornNorm splitUnit = -1 := by
  simp [splitUnit, zornPlus, zornMinus, zornNorm_apply, zornNormFun, dot]

theorem norm_splitAxis (i : Fin 3) : zornNorm (splitAxis i) = -1 := by
  fin_cases i <;>
    simp [splitAxis, chiralUpperBasis, chiralLowerBasis, zornNorm_apply,
      zornNormFun, dot]

/-- Flexibility is an equality of actual left/right multiplication operators. -/
theorem left_right_flexible (a : ZornMatrix ℝ) :
    leftMulLinear a * rightMulLinear a = rightMulLinear a * leftMulLinear a := by
  apply LinearMap.ext
  intro w
  change a * (w * a) = (a * w) * a
  apply ZornMatrix.ext
  · simp [ZornMatrix.mul, dot, cross]; ring
  · simp [ZornMatrix.mul, dot, cross]; ring
  · funext i; fin_cases i <;> simp [ZornMatrix.mul, dot, cross] <;> ring
  · funext i; fin_cases i <;> simp [ZornMatrix.mul, dot, cross] <;> ring

theorem right_conjugate_contraction (a : ZornMatrix ℝ) :
    rightMulLinear a * rightMulLinear (zornConj a) =
      zornNorm a • (1 : Module.End ℝ (ZornMatrix ℝ)) := by
  apply LinearMap.ext
  intro w
  change (w * zornConj a) * a = zornNorm a • w
  apply ZornMatrix.ext
  · simp [ZornMatrix.mul, dot, cross, zornConj, zornNorm_apply, zornNormFun]; ring
  · simp [ZornMatrix.mul, dot, cross, zornConj, zornNorm_apply, zornNormFun]; ring
  · funext i; fin_cases i <;>
      simp [ZornMatrix.mul, dot, cross, zornConj, zornNorm_apply, zornNormFun] <;> ring
  · funext i; fin_cases i <;>
      simp [ZornMatrix.mul, dot, cross, zornConj, zornNorm_apply, zornNormFun] <;> ring

/-- The left/right commutator is the negative associator, with order explicit. -/
theorem left_right_commutator (a b w : ZornMatrix ℝ) :
    (leftMulLinear a * rightMulLinear b - rightMulLinear b * leftMulLinear a) w =
      -((a * w) * b - a * (w * b)) := by
  change a * (w * b) - (a * w) * b = -((a * w) * b - a * (w * b))
  abel

end InfoGeometry.Canonical.ZornSignedConvention
