/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.HestenesNaturalConeStandardForm
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem selfDuality_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

variable {R : Type*} [CommRing R] [Preorder R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

variable (Tr : ClPlus Q →ₗ[R] R)

/--
The Hilbert-Schmidt Inner Product.
For ClPlus Q, this is `\langle X, Y \rangle_{HS} = Tr (X^† * Y)`.
-/
def hsInnerProduct (X Y : ClPlus Q) : R :=
  Tr (L_action Q (J_mod Q v0 X) Y)

/--
The Dual Cone `\mathcal{P}^\circ` relative to the Hilbert-Schmidt inner product.
-/
def DualCone : Set (ClPlus Q) :=
  { Y | ∀ X ∈ NaturalCone Q v0, hsInnerProduct Q v0 Tr X Y ≥ 0 }

/-- The zero element belongs to the Hilbert-Schmidt dual cone `DualCone Q v0 Tr`. -/
theorem zero_mem_dualCone : (0 : ClPlus Q) ∈ DualCone Q v0 Tr := by
  intro X _hX
  have hL : L_action Q (J_mod Q v0 X) (0 : ClPlus Q) = 0 := by
    ext
    simp [L_action]
  simp [hsInnerProduct, hL]

section NonCommRingPositiveCone

variable (B : Type*) [Ring B] [StarRing B]

/-- Algebraic positive cone `{ x : B | ∃ y : B, x = star y * y }` in any non-commutative `*-ring` `[Ring B] [StarRing B]`. -/
def ringPositiveCone : Set B :=
  { x | ∃ y : B, x = star y * y }

theorem zero_mem_ringPositiveCone : (0 : B) ∈ ringPositiveCone B :=
  ⟨0, by simp⟩

theorem one_mem_ringPositiveCone : (1 : B) ∈ ringPositiveCone B :=
  ⟨1, by simp⟩

theorem star_eq_self_of_mem_ringPositiveCone {x : B} (hx : x ∈ ringPositiveCone B) :
    star x = x := by
  rcases hx with ⟨y, rfl⟩
  simp [star_mul]

end NonCommRingPositiveCone

end InfoGeometry.Clifford.Hestenes
