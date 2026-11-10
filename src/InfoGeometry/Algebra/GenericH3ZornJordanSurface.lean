/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornCubicOperators
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Generic cubic Jordan surface for `H3Zorn`

This is the coefficient-field-independent predecessor of the real-only
`candidateJordanMul`.  It exposes the same cubic construction over any field
and therefore provides the correct carrier for exact rational certificates.
No claim about a basis or a rank certificate is made here.
-/

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingJordanSurface

variable {B : Type*} [Ring B]

/-- Unnormalized Jordan anticommutator product `X ∘₂ Y = X * Y + Y * X` over any
non-commutative ring `[Ring B]` (without requiring `2⁻¹` or commutativity of `B`). -/
def ringJordanMul2 (X Y : B) : B :=
  X * Y + Y * X

@[simp] theorem ringJordanMul2_comm (X Y : B) :
    ringJordanMul2 X Y = ringJordanMul2 Y X := by
  dsimp [ringJordanMul2]
  abel

theorem ringJordanMul2_add_left (X₁ X₂ Y : B) :
    ringJordanMul2 (X₁ + X₂) Y = ringJordanMul2 X₁ Y + ringJordanMul2 X₂ Y := by
  dsimp [ringJordanMul2]
  noncomm_ring

theorem ringJordanMul2_add_right (X Y₁ Y₂ : B) :
    ringJordanMul2 X (Y₁ + Y₂) = ringJordanMul2 X Y₁ + ringJordanMul2 X Y₂ := by
  dsimp [ringJordanMul2]
  noncomm_ring

/-- Inner derivation `[L_A, L_C](X)` of the unnormalized Jordan product over any
non-commutative ring `[Ring B]`. -/
def ringJordanInnerAction2 (A C X : B) : B :=
  ringJordanMul2 A (ringJordanMul2 C X) - ringJordanMul2 C (ringJordanMul2 A X)

theorem ringJordanInnerAction2_add (A C X Y : B) :
    ringJordanInnerAction2 A C (X + Y) =
      ringJordanInnerAction2 A C X + ringJordanInnerAction2 A C Y := by
  dsimp [ringJordanInnerAction2, ringJordanMul2]
  noncomm_ring

/-- In any associative ring `[Ring B]`, the Jordan inner derivation `[L_A, L_C](X)`
equals the double commutator `[[A, C], X] = (A * C - C * A) * X - X * (A * C - C * A)`. -/
theorem ringJordanInnerAction2_eq_commutator_ad (A C X : B) :
    ringJordanInnerAction2 A C X =
      (A * C - C * A) * X - X * (A * C - C * A) := by
  dsimp [ringJordanInnerAction2, ringJordanMul2]
  noncomm_ring

end NonCommRingJordanSurface

variable {R : Type*} [CommRing R] [Inv R]

/-- The cubic Jordan product induced by the generic `H3Zorn` trilinear form. -/
noncomputable def cubicJordanMul (X Y : H3Zorn R) : H3Zorn R :=
  (2 : R)⁻¹ • H3Zorn.T X 1 Y

@[simp] theorem cubicJordanMul_comm (X Y : H3Zorn R) :
    cubicJordanMul X Y = cubicJordanMul Y X := by
  simp only [cubicJordanMul, H3Zorn.T_symm_outer]

theorem cubicJordanMul_add_left (X₁ X₂ Y : H3Zorn R) :
    cubicJordanMul (X₁ + X₂) Y =
      cubicJordanMul X₁ Y + cubicJordanMul X₂ Y := by
  simp only [cubicJordanMul, H3Zorn.T_add_left, smul_add]

theorem cubicJordanMul_add_right (X Y₁ Y₂ : H3Zorn R) :
    cubicJordanMul X (Y₁ + Y₂) =
      cubicJordanMul X Y₁ + cubicJordanMul X Y₂ := by
  rw [cubicJordanMul_comm, cubicJordanMul_add_left]
  rw [cubicJordanMul_comm Y₁ X, cubicJordanMul_comm Y₂ X]

theorem cubicJordanMul_smul_left (r : R) (X Y : H3Zorn R) :
    cubicJordanMul (r • X) Y = r • cubicJordanMul X Y := by
  simp only [cubicJordanMul, H3Zorn.T_smul_left, smul_smul]
  module

theorem cubicJordanMul_smul_right (r : R) (X Y : H3Zorn R) :
    cubicJordanMul X (r • Y) = r • cubicJordanMul X Y := by
  rw [cubicJordanMul_comm, cubicJordanMul_smul_left]
  rw [cubicJordanMul_comm Y X]

/-- The pointwise commutator of two cubic Jordan left multiplications.  This
is the coefficient-field-independent action used by exact certificates. -/
noncomputable def cubicJordanInnerAction (A B X : H3Zorn R) : H3Zorn R :=
  cubicJordanMul A (cubicJordanMul B X) -
    cubicJordanMul B (cubicJordanMul A X)

theorem cubicJordanInnerAction_add (A B X Y : H3Zorn R) :
    cubicJordanInnerAction A B (X + Y) =
      cubicJordanInnerAction A B X + cubicJordanInnerAction A B Y := by
  simp only [cubicJordanInnerAction, cubicJordanMul_add_right]
  abel

theorem cubicJordanInnerAction_smul (r : R) (A B X : H3Zorn R) :
    cubicJordanInnerAction A B (r • X) =
      r • cubicJordanInnerAction A B X := by
  simp only [cubicJordanInnerAction, cubicJordanMul_smul_right, smul_sub]

theorem cubicJordanInnerAction_apply (A B X : H3Zorn R) :
    cubicJordanInnerAction A B X =
      cubicJordanMul A (cubicJordanMul B X) -
        cubicJordanMul B (cubicJordanMul A X) := rfl

end InfoGeometry.Algebra
