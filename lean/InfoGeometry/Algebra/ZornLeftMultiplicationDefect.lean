/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftCAR

/-!
# Associator defect of the native Zorn left action

The native Zorn left-multiplication map preserves squares and polarized products.
Its failure to preserve ordered products is precisely the associator.
No Filippov or Nambu–Poisson identity is asserted.
-/

namespace InfoGeometry.Algebra.ZornLeftCAR

open ZornPinorReconstruction

noncomputable section

/-- Difference between multiplication by a product and composition of actions. -/
def multiplicationDefect (X Y : Z) : Module.End ℝ Z :=
  leftMultiplication (ZornVectorMatrix.mul X Y) -
    leftMultiplication X * leftMultiplication Y

@[simp] theorem multiplicationDefect_apply (X Y W : Z) :
    multiplicationDefect X Y W = ZornVectorMatrix.associator X Y W := rfl

/-- Polarization makes the multiplication defect skew in its two inputs. -/
theorem multiplicationDefect_swap (X Y : Z) :
    multiplicationDefect Y X = -multiplicationDefect X Y := by
  have h := leftMultiplication_anticommutator X Y
  rw [map_add] at h
  unfold multiplicationDefect
  have h' := congrArg (fun T : Module.End ℝ Z =>
    T - leftMultiplication X * leftMultiplication Y -
      leftMultiplication (ZornVectorMatrix.mul Y X)) h
  have hn := congrArg Neg.neg h'
  convert hn using 1 <;> abel

/-- Exact criterion for a fixed pair to act multiplicatively on the whole module. -/
theorem leftMultiplication_mul_eq_iff (X Y : Z) :
    leftMultiplication (ZornVectorMatrix.mul X Y) =
        leftMultiplication X * leftMultiplication Y ↔
      ∀ W, ZornVectorMatrix.associator X Y W = ZornVectorMatrix.zero := by
  constructor
  · intro h W
    have he := LinearMap.congr_fun h W
    change ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y) W =
      ZornVectorMatrix.mul X (ZornVectorMatrix.mul Y W) at he
    change ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y) W -
      ZornVectorMatrix.mul X (ZornVectorMatrix.mul Y W) = 0
    exact sub_eq_zero.mpr he
  · intro h
    apply LinearMap.ext
    intro W
    exact sub_eq_zero.mp (h W)

/-- The commutator correction is twice the associator, with the owner's sign. -/
theorem leftMultiplication_commutator_defect (X Y : Z) :
    leftMultiplication X * leftMultiplication Y -
        leftMultiplication Y * leftMultiplication X =
      leftMultiplication (ZornVectorMatrix.commutator X Y) -
        2 • multiplicationDefect X Y := by
  have h := multiplicationDefect_swap X Y
  change leftMultiplication X * leftMultiplication Y -
      leftMultiplication Y * leftMultiplication X =
    leftMultiplication (ZornVectorMatrix.mul X Y - ZornVectorMatrix.mul Y X) -
      2 • multiplicationDefect X Y
  rw [map_sub, two_nsmul]
  calc
    _ = (leftMultiplication (ZornVectorMatrix.mul X Y) -
        leftMultiplication (ZornVectorMatrix.mul Y X)) -
        multiplicationDefect X Y + multiplicationDefect Y X := by
          unfold multiplicationDefect
          abel
    _ = _ := by rw [h]; abel

end
end InfoGeometry.Algebra.ZornLeftCAR
