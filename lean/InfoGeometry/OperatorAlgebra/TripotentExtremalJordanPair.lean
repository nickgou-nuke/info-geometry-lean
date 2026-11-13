/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentIntegerGrading
import InfoGeometry.Canonical.TKKJordanPairData
import InfoGeometry.OperatorAlgebra.PeirceSpine.PullbackTriple
import Mathlib.Algebra.Lie.Subalgebra

/-!
# The actual extreme Jordan pair inside a Lie subalgebra

Intersect any native ordinary Lie subalgebra with the two extreme integer
grades. The double commutator equals the existing associative Jordan triple
and supplies an actual instance of the repository's `JordanPair` data.
Outer symmetry, the fundamental identities and all three-variable linearity
laws are proved on the original carrier. Adjoint stability is needed for a
decomposition of the whole Lie subalgebra, but not for this extreme pair.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TripotentExtremalJordanPair

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.OperatorAlgebra.PeirceSpine

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Products of two elements of the same extreme grade vanish. -/
theorem same_extreme_product_eq_zero {S x z : A} (hS : S * S * S = S)
    {i : ℤ} (hi : i = -2 ∨ i = 2)
    (hx : x ∈ adGrade S i) (hz : z ∈ adGrade S i) : x * z = 0 := by
  have h := mul_mem_adGrade_add hx hz
  have hout : i + i < -2 ∨ 2 < i + i := by omega
  rw [adGrade_eq_bot_of_outside hS hout] at h
  exact h

/-- The double commutator is the associative Jordan triple on extreme
outer arguments; the middle argument can be any element of the algebra. -/
theorem double_lie_eq_jordanTriple {S x z : A} (hS : S * S * S = S)
    {i : ℤ} (hi : i = -2 ∨ i = 2)
    (hx : x ∈ adGrade S i) (hz : z ∈ adGrade S i) (y : A) :
    ⁅⁅x, y⁆, z⁆ = jordanTriple x y z := by
  have hxz := same_extreme_product_eq_zero hS hi hx hz
  have hzx := same_extreme_product_eq_zero hS hi hz hx
  calc
    ⁅⁅x, y⁆, z⁆ = x * y * z + z * y * x - y * (x * z) - (z * x) * y := by
      simp only [Ring.lie_def]
      noncomm_ring
    _ = jordanTriple x y z := by rw [hxz, hzx]; simp [jordanTriple]

/-- Closure of the actual triple in a Lie-subalgebra extreme intersection. -/
theorem jordanTriple_mem_extreme_intersection {S x y z : A}
    (hS : S * S * S = S) (L : LieSubalgebra ℝ A)
    {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (hx : x ∈ L.toSubmodule ⊓ adGrade S i)
    (hy : y ∈ L.toSubmodule ⊓ adGrade S j)
    (hz : z ∈ L.toSubmodule ⊓ adGrade S i) :
    jordanTriple x y z ∈ L.toSubmodule ⊓ adGrade S i := by
  constructor
  · rw [← double_lie_eq_jordanTriple hS hi hx.2 hz.2]
    exact L.lie_mem (L.lie_mem hx.1 hy.1) hz.1
  · have hxyz := mul_mem_adGrade_add (mul_mem_adGrade_add hx.2 hy.2) hz.2
    have hzyx := mul_mem_adGrade_add (mul_mem_adGrade_add hz.2 hy.2) hx.2
    simpa only [hij, zero_add] using add_mem hxyz hzyx

/-- The subtype triple is constructed from multiplication, with closure
proved above. Its algebraic identities are not assumed as fields. -/
def restrictedExtremeTriple {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (x : L.toSubmodule ⊓ adGrade S i) (y : L.toSubmodule ⊓ adGrade S j)
    (z : L.toSubmodule ⊓ adGrade S i) : L.toSubmodule ⊓ adGrade S i :=
  ⟨jordanTriple (x : A) (y : A) (z : A),
    jordanTriple_mem_extreme_intersection hS L hi hij x.property y.property z.property⟩

/-- Agreement with the nested ordinary Lie bracket in the ambient algebra. -/
theorem coe_restrictedExtremeTriple_eq_double_lie {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (x : L.toSubmodule ⊓ adGrade S i) (y : L.toSubmodule ⊓ adGrade S j)
    (z : L.toSubmodule ⊓ adGrade S i) :
    (restrictedExtremeTriple hS L hi hij x y z : A) = ⁅⁅(x : A), (y : A)⁆, (z : A)⁆ :=
  (double_lie_eq_jordanTriple hS hi x.property.2 z.property.2 (y : A)).symm

/-- Additivity in the first argument, simultaneously for both extremes. -/
theorem restrictedExtremeTriple_add_left {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (x x' z : L.toSubmodule ⊓ adGrade S i) (y : L.toSubmodule ⊓ adGrade S j) :
    restrictedExtremeTriple hS L hi hij (x + x') y z =
      restrictedExtremeTriple hS L hi hij x y z +
        restrictedExtremeTriple hS L hi hij x' y z := by
  apply Subtype.ext
  change jordanTriple ((x : A) + x') y z = jordanTriple x y z + jordanTriple x' y z
  simp only [jordanTriple, add_mul, mul_add]
  abel

/-- Additivity in the middle argument. -/
theorem restrictedExtremeTriple_add_middle {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (x z : L.toSubmodule ⊓ adGrade S i) (y y' : L.toSubmodule ⊓ adGrade S j) :
    restrictedExtremeTriple hS L hi hij x (y + y') z =
      restrictedExtremeTriple hS L hi hij x y z +
        restrictedExtremeTriple hS L hi hij x y' z := by
  apply Subtype.ext
  change jordanTriple x ((y : A) + y') z = jordanTriple x y z + jordanTriple x y' z
  simp only [jordanTriple, add_mul, mul_add]
  abel

/-- Additivity in the last argument. -/
theorem restrictedExtremeTriple_add_right {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (x z z' : L.toSubmodule ⊓ adGrade S i) (y : L.toSubmodule ⊓ adGrade S j) :
    restrictedExtremeTriple hS L hi hij x y (z + z') =
      restrictedExtremeTriple hS L hi hij x y z +
        restrictedExtremeTriple hS L hi hij x y z' := by
  apply Subtype.ext
  change jordanTriple x y ((z : A) + z') = jordanTriple x y z + jordanTriple x y z'
  simp only [jordanTriple, add_mul, mul_add]
  abel

/-- Real linearity in the first argument. -/
theorem restrictedExtremeTriple_smul_left {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (r : ℝ) (x z : L.toSubmodule ⊓ adGrade S i) (y : L.toSubmodule ⊓ adGrade S j) :
    restrictedExtremeTriple hS L hi hij (r • x) y z =
      r • restrictedExtremeTriple hS L hi hij x y z := by
  apply Subtype.ext
  change jordanTriple (r • (x : A)) y z = r • jordanTriple x y z
  simp only [jordanTriple, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add]

/-- Real linearity in the middle argument. -/
theorem restrictedExtremeTriple_smul_middle {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (r : ℝ) (x z : L.toSubmodule ⊓ adGrade S i) (y : L.toSubmodule ⊓ adGrade S j) :
    restrictedExtremeTriple hS L hi hij x (r • y) z =
      r • restrictedExtremeTriple hS L hi hij x y z := by
  apply Subtype.ext
  change jordanTriple x (r • (y : A)) z = r • jordanTriple x y z
  simp only [jordanTriple, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add]

/-- Real linearity in the last argument. -/
theorem restrictedExtremeTriple_smul_right {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) {i j : ℤ} (hi : i = -2 ∨ i = 2) (hij : i + j = 0)
    (r : ℝ) (x z : L.toSubmodule ⊓ adGrade S i) (y : L.toSubmodule ⊓ adGrade S j) :
    restrictedExtremeTriple hS L hi hij x y (r • z) =
      r • restrictedExtremeTriple hS L hi hij x y z := by
  apply Subtype.ext
  change jordanTriple x y (r • (z : A)) = r • jordanTriple x y z
  simp only [jordanTriple, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add]

/-- The concrete extreme Jordan pair of any native Lie subalgebra. The
ambient pair is obtained by taking `L = ⊤`. No involution is required. -/
def lieSubalgebraExtremeJordanPair {S : A} (hS : S * S * S = S)
    (L : LieSubalgebra ℝ A) : TKKJordanPairData.JordanPair ℝ where
  Vplus := L.toSubmodule ⊓ adGrade S 2
  Vminus := L.toSubmodule ⊓ adGrade S (-2)
  plus_add := inferInstance
  minus_add := inferInstance
  plus_module := inferInstance
  minus_module := inferInstance
  triplePlus := restrictedExtremeTriple hS L (Or.inr rfl) (by norm_num)
  tripleMinus := restrictedExtremeTriple hS L (Or.inl rfl) (by norm_num)
  triplePlus_outer := by
    intro x y z
    apply Subtype.ext
    exact add_comm ((x : A) * y * z) ((z : A) * y * x)
  tripleMinus_outer := by
    intro x y z
    apply Subtype.ext
    exact add_comm ((x : A) * y * z) ((z : A) * y * x)
  triplePlus_fundamental := by
    intro x u w y v
    apply Subtype.ext
    change jordanTriple (x : A) y (jordanTriple u v w) -
        jordanTriple u v (jordanTriple x y w) =
      jordanTriple (jordanTriple x y u) v w - jordanTriple u (jordanTriple y x v) w
    rw [jordanTriple_fundamental]
    abel
  tripleMinus_fundamental := by
    intro x u w y v
    apply Subtype.ext
    change jordanTriple (x : A) y (jordanTriple u v w) -
        jordanTriple u v (jordanTriple x y w) =
      jordanTriple (jordanTriple x y u) v w - jordanTriple u (jordanTriple y x v) w
    rw [jordanTriple_fundamental]
    abel

end InfoGeometry.OperatorAlgebra.TripotentExtremalJordanPair
