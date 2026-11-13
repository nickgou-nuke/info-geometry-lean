/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces
import InfoGeometry.Canonical.TKKJordanPairData
import Mathlib.Algebra.Lie.Subalgebra

/-!
# The Jordan pair of extreme tripotent Lie grades

Inside any ordinary Lie subalgebra of an associative real algebra, opposite
extreme grades carry the triple product `[[x,y],z]`. Weight addition gives
closure; absence of degree `±4` gives outer symmetry; the native Lie Leibniz
identity gives the two fundamental Jordan-pair identities. All identities
required by the existing `TKKJordanPairData.JordanPair` owner are proved.

This construction does not assert that either extreme grade is nonzero, nor
that skew-adjoint elements are closed under associative anticommutators.
-/

noncomputable section

namespace InfoGeometry.Core.TripotentJordanPair

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Each extreme integer grade is abelian for the ordinary Lie bracket. -/
theorem lie_eq_zero_of_mem_same_extreme {S X Z : A} (hS : S * S * S = S)
    {k : ℤ} (hk : k = 2 ∨ k = -2)
    (hX : X ∈ adGrade S k) (hZ : Z ∈ adGrade S k) : ⁅X, Z⁆ = 0 := by
  rw [adGrade_eq_eigenspace] at hX hZ
  apply lie_eq_zero_of_weight_not_mem hS hX hZ
  rcases hk with rfl | rfl <;> rintro ⟨j, hj⟩ <;>
    cases j <;> norm_num [fiveGradeValue] at hj

/-- Restrict the ordinary double commutator to opposite homogeneous
intersections with a native Lie subalgebra. -/
def extremeTriple (p : LieSubalgebra ℝ A) (S : A) (k : ℤ)
    (X : p.toSubmodule ⊓ adGrade S k)
    (Y : p.toSubmodule ⊓ adGrade S (-k))
    (Z : p.toSubmodule ⊓ adGrade S k) : p.toSubmodule ⊓ adGrade S k :=
  ⟨⁅⁅(X : A), (Y : A)⁆, (Z : A)⁆, by
    constructor
    · exact p.lie_mem (p.lie_mem X.property.1 Y.property.1) Z.property.1
    · have hXY := commutator_mem_adGrade_add X.property.2 Y.property.2
      have hXYZ := commutator_mem_adGrade_add hXY Z.property.2
      simpa only [add_neg_cancel, zero_add, Ring.lie_def] using hXYZ⟩

/-- The triple product is additive in its first argument. -/
theorem extremeTriple_add_left (p : LieSubalgebra ℝ A) (S : A) (k : ℤ)
    (X X' Z : p.toSubmodule ⊓ adGrade S k)
    (Y : p.toSubmodule ⊓ adGrade S (-k)) :
    extremeTriple p S k (X + X') Y Z =
      extremeTriple p S k X Y Z + extremeTriple p S k X' Y Z := by
  apply Subtype.ext
  change ⁅⁅(X : A) + (X' : A), (Y : A)⁆, (Z : A)⁆ =
    ⁅⁅(X : A), (Y : A)⁆, (Z : A)⁆ + ⁅⁅(X' : A), (Y : A)⁆, (Z : A)⁆
  simp only [add_lie]

/-- The triple product is additive in its middle argument. -/
theorem extremeTriple_add_middle (p : LieSubalgebra ℝ A) (S : A) (k : ℤ)
    (X Z : p.toSubmodule ⊓ adGrade S k)
    (Y Y' : p.toSubmodule ⊓ adGrade S (-k)) :
    extremeTriple p S k X (Y + Y') Z =
      extremeTriple p S k X Y Z + extremeTriple p S k X Y' Z := by
  apply Subtype.ext
  change ⁅⁅(X : A), (Y : A) + (Y' : A)⁆, (Z : A)⁆ =
    ⁅⁅(X : A), (Y : A)⁆, (Z : A)⁆ + ⁅⁅(X : A), (Y' : A)⁆, (Z : A)⁆
  simp only [lie_add, add_lie]

/-- The triple product is additive in its last argument. -/
theorem extremeTriple_add_right (p : LieSubalgebra ℝ A) (S : A) (k : ℤ)
    (X Z Z' : p.toSubmodule ⊓ adGrade S k)
    (Y : p.toSubmodule ⊓ adGrade S (-k)) :
    extremeTriple p S k X Y (Z + Z') =
      extremeTriple p S k X Y Z + extremeTriple p S k X Y Z' := by
  apply Subtype.ext
  change ⁅⁅(X : A), (Y : A)⁆, (Z : A) + (Z' : A)⁆ =
    ⁅⁅(X : A), (Y : A)⁆, (Z : A)⁆ + ⁅⁅(X : A), (Y : A)⁆, (Z' : A)⁆
  simp only [lie_add]

/-- The triple product is real linear in its first argument. -/
theorem extremeTriple_smul_left (p : LieSubalgebra ℝ A) (S : A) (k : ℤ)
    (c : ℝ) (X Z : p.toSubmodule ⊓ adGrade S k)
    (Y : p.toSubmodule ⊓ adGrade S (-k)) :
    extremeTriple p S k (c • X) Y Z = c • extremeTriple p S k X Y Z := by
  apply Subtype.ext
  change ⁅⁅c • (X : A), (Y : A)⁆, (Z : A)⁆ =
    c • ⁅⁅(X : A), (Y : A)⁆, (Z : A)⁆
  simp only [smul_lie]

/-- The triple product is real linear in its middle argument. -/
theorem extremeTriple_smul_middle (p : LieSubalgebra ℝ A) (S : A) (k : ℤ)
    (c : ℝ) (X Z : p.toSubmodule ⊓ adGrade S k)
    (Y : p.toSubmodule ⊓ adGrade S (-k)) :
    extremeTriple p S k X (c • Y) Z = c • extremeTriple p S k X Y Z := by
  apply Subtype.ext
  change ⁅⁅(X : A), c • (Y : A)⁆, (Z : A)⁆ =
    c • ⁅⁅(X : A), (Y : A)⁆, (Z : A)⁆
  simp only [lie_smul, smul_lie]

/-- The triple product is real linear in its last argument. -/
theorem extremeTriple_smul_right (p : LieSubalgebra ℝ A) (S : A) (k : ℤ)
    (c : ℝ) (X Z : p.toSubmodule ⊓ adGrade S k)
    (Y : p.toSubmodule ⊓ adGrade S (-k)) :
    extremeTriple p S k X Y (c • Z) = c • extremeTriple p S k X Y Z := by
  apply Subtype.ext
  change ⁅⁅(X : A), (Y : A)⁆, c • (Z : A)⁆ =
    c • ⁅⁅(X : A), (Y : A)⁆, (Z : A)⁆
  simp only [lie_smul]

private theorem double_lie_outer (X Y Z : A) (hXZ : ⁅X, Z⁆ = 0) :
    ⁅⁅X, Y⁆, Z⁆ = ⁅⁅Z, Y⁆, X⁆ := by
  have h := leibniz_lie X Y Z
  rw [hXZ, lie_zero, add_zero] at h
  calc
    ⁅⁅X, Y⁆, Z⁆ = ⁅X, ⁅Y, Z⁆⁆ := h.symm
    _ = ⁅⁅Z, Y⁆, X⁆ := by rw [← lie_skew Y Z, lie_neg, lie_skew]

/-- Commutativity of the extreme grade supplies the required outer symmetry. -/
theorem extremeTriple_outer (p : LieSubalgebra ℝ A) {S : A}
    (hS : S * S * S = S) {k : ℤ} (hk : k = 2 ∨ k = -2)
    (X Z : p.toSubmodule ⊓ adGrade S k)
    (Y : p.toSubmodule ⊓ adGrade S (-k)) :
    extremeTriple p S k X Y Z = extremeTriple p S k Z Y X := by
  apply Subtype.ext
  exact double_lie_outer (X : A) (Y : A) (Z : A)
    (lie_eq_zero_of_mem_same_extreme hS hk X.property.2 Z.property.2)

private theorem double_lie_fundamental (X Y U V W : A) :
    ⁅⁅X, Y⁆, ⁅⁅U, V⁆, W⁆⁆ - ⁅⁅U, V⁆, ⁅⁅X, Y⁆, W⁆⁆ =
      ⁅⁅⁅⁅X, Y⁆, U⁆, V⁆, W⁆ - ⁅⁅U, ⁅⁅Y, X⁆, V⁆⁆, W⁆ := by
  calc
    _ = ⁅⁅⁅X, Y⁆, ⁅U, V⁆⁆, W⁆ := by
      rw [leibniz_lie ⁅X, Y⁆ ⁅U, V⁆ W, add_sub_cancel_right]
    _ = ⁅⁅⁅⁅X, Y⁆, U⁆, V⁆, W⁆ + ⁅⁅U, ⁅⁅X, Y⁆, V⁆⁆, W⁆ := by
      rw [leibniz_lie ⁅X, Y⁆ U V, add_lie]
    _ = _ := by
      rw [← lie_skew Y X, neg_lie, lie_neg, neg_lie, sub_neg_eq_add]

/-- The existing Jordan-pair structure, now constructed from the actual
extreme intersections and proved ordinary-Lie identities. -/
def tripotentExtremeJordanPair (p : LieSubalgebra ℝ A) (S : A)
    (hS : S * S * S = S) : TKKJordanPairData.JordanPair ℝ where
  Vplus := p.toSubmodule ⊓ adGrade S 2
  Vminus := p.toSubmodule ⊓ adGrade S (-2)
  plus_add := inferInstance
  minus_add := inferInstance
  plus_module := inferInstance
  minus_module := inferInstance
  triplePlus := extremeTriple p S 2
  tripleMinus := extremeTriple p S (-2)
  triplePlus_outer := by
    intro X Y Z
    exact extremeTriple_outer p hS (Or.inl rfl) X Z Y
  tripleMinus_outer := by
    intro X Y Z
    exact extremeTriple_outer p hS (Or.inr rfl) X Z Y
  triplePlus_fundamental := by
    intro X U W Y V
    apply Subtype.ext
    exact double_lie_fundamental (X : A) (Y : A) (U : A) (V : A) (W : A)
  tripleMinus_fundamental := by
    intro X U W Y V
    apply Subtype.ext
    exact double_lie_fundamental (X : A) (Y : A) (U : A) (V : A) (W : A)

end InfoGeometry.Core.TripotentJordanPair
