/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftCAR
import InfoGeometry.Algebra.ZornDerivationBridge

/-! # Invertibility of the native Zorn left action

The carrier is the existing real eight-dimensional `ZornVectorMatrix ℝ`.
Conjugate contraction uses alternativity through `kirmse_left`, never
associativity of octonion multiplication. Composition in `Module.End` is
associative. No positivity of the split norm is required.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornLeftCAR

open ZornPinorReconstruction

theorem conjugate_leftMultiplication_mul (z : Z) :
    leftMultiplication (ZornVectorMatrix.conj z) * leftMultiplication z =
      ZornVectorMatrix.norm z • (1 : Module.End ℝ Z) := by
  apply LinearMap.ext
  intro w
  change ZornVectorMatrix.mul (ZornVectorMatrix.conj z) (ZornVectorMatrix.mul z w) =
    ZornVectorMatrix.smul (ZornVectorMatrix.norm z) w
  exact ZornVectorMatrix.kirmse_left z w

theorem leftMultiplication_mul_conjugate (z : Z) :
    leftMultiplication z * leftMultiplication (ZornVectorMatrix.conj z) =
      ZornVectorMatrix.norm z • (1 : Module.End ℝ Z) := by
  simpa only [ZornVectorMatrix.conj_conj, ZornVectorMatrix.norm_conj] using
    conjugate_leftMultiplication_mul (ZornVectorMatrix.conj z)

/-- The explicit inverse is the norm-scaled conjugate left action. -/
def leftMultiplicationUnit (z : Z) (hz : ZornVectorMatrix.norm z ≠ 0) :
    (Module.End ℝ Z)ˣ where
  val := leftMultiplication z
  inv := (ZornVectorMatrix.norm z)⁻¹ • leftMultiplication (ZornVectorMatrix.conj z)
  val_inv := by
    rw [mul_smul_comm, leftMultiplication_mul_conjugate, smul_smul,
      inv_mul_cancel₀ hz, one_smul]
  inv_val := by
    rw [smul_mul_assoc, conjugate_leftMultiplication_mul, smul_smul,
      inv_mul_cancel₀ hz, one_smul]

/-- A nonzero split norm, of either sign, is exactly the invertibility criterion. -/
theorem leftMultiplication_isUnit_iff (z : Z) :
    IsUnit (leftMultiplication z) ↔ ZornVectorMatrix.norm z ≠ 0 := by
  constructor
  · rintro ⟨u, hu⟩ hz
    let w := (↑(u⁻¹) : Module.End ℝ Z) ZornVectorMatrix.one
    have hw : ZornVectorMatrix.mul z w = ZornVectorMatrix.one := by
      change leftMultiplication z ((↑(u⁻¹) : Module.End ℝ Z) ZornVectorMatrix.one) = _
      rw [← hu]
      exact LinearMap.congr_fun u.val_inv ZornVectorMatrix.one
    have hn := congrArg ZornVectorMatrix.norm hw
    rw [ZornVectorMatrix.norm_mul, hz, zero_mul] at hn
    norm_num [ZornVectorMatrix.norm, ZornVectorMatrix.one, ZornVec3.dot] at hn
  · intro hz
    exact ⟨leftMultiplicationUnit z hz, rfl⟩

end InfoGeometry.Algebra.ZornLeftCAR
