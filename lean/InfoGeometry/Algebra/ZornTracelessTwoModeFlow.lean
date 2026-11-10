/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornAlternativeLaws
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Zorn traceless two-mode polynomial flow

In the repository's actual Zorn multiplication convention the Casimir is
`α² + dot v w`, not `α² - dot v w`. This is a polynomial two-mode flow,
not a general analytic exponential or a global Lie-group representation.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingTwoModeFlow

variable {B : Type*} [Ring B]

/-- Two-mode polynomial flow `c + s * X` in a non-commutative ring `[Ring B]`. -/
def ringTwoModeExp (c s X : B) : B :=
  c + s * X

/-- Over any non-commutative ring `[Ring B]`, if `c₂` and `s₂` commute with `X`,
then the two-mode polynomial flow satisfies the Cayley–Hamilton multiplication law:
`(c₁ + s₁ * X) * (c₂ + s₂ * X) = (c₁ * c₂ + s₁ * s₂ * (X * X)) + (c₁ * s₂ + s₁ * c₂) * X`. -/
theorem ringTwoModeExp_mul_of_commute (c₁ s₁ c₂ s₂ X : B)
    (hc₂X : Commute c₂ X) (hs₂X : Commute s₂ X) :
    ringTwoModeExp c₁ s₁ X * ringTwoModeExp c₂ s₂ X =
      ringTwoModeExp (c₁ * c₂ + s₁ * s₂ * (X * X)) (c₁ * s₂ + s₁ * c₂) X := by
  dsimp [ringTwoModeExp]
  have h1 : (s₁ * X) * c₂ = s₁ * c₂ * X := by
    calc
      (s₁ * X) * c₂ = s₁ * (X * c₂) := by noncomm_ring
      _ = s₁ * (c₂ * X) := by rw [hc₂X.symm.eq]
      _ = s₁ * c₂ * X := by noncomm_ring
  have h2 : (s₁ * X) * (s₂ * X) = s₁ * s₂ * (X * X) := by
    calc
      (s₁ * X) * (s₂ * X) = s₁ * (X * s₂) * X := by noncomm_ring
      _ = s₁ * (s₂ * X) * X := by rw [hs₂X.symm.eq]
      _ = s₁ * s₂ * (X * X) := by noncomm_ring
  calc
    (c₁ + s₁ * X) * (c₂ + s₂ * X)
      = c₁ * c₂ + c₁ * (s₂ * X) + (s₁ * X) * c₂ + (s₁ * X) * (s₂ * X) := by noncomm_ring
    _ = c₁ * c₂ + c₁ * (s₂ * X) + s₁ * c₂ * X + s₁ * s₂ * (X * X) := by rw [h1, h2]
    _ = (c₁ * c₂ + s₁ * s₂ * (X * X)) + (c₁ * s₂ + s₁ * c₂) * X := by noncomm_ring

/-- Over any non-commutative ring `[Ring B]`, if `c` and `s` commute with `X` and
with each other, then `(c + s * X) * (c - s * X) = c * c - s * s * (X * X)`. -/
theorem ringTwoModeExp_mul_opposite_of_commute (c s X : B)
    (hcX : Commute c X) (hsX : Commute s X) (hcs : Commute c s) :
    ringTwoModeExp c s X * ringTwoModeExp c (-s) X =
      c * c - s * s * (X * X) := by
  have hnsX : Commute (-s) X := hsX.neg_left
  rw [ringTwoModeExp_mul_of_commute c s c (-s) X hcX hnsX]
  dsimp [ringTwoModeExp]
  have hcancel : c * (-s) + s * c = 0 := by
    calc
      c * (-s) + s * c = - (c * s) + s * c := by noncomm_ring
      _ = - (s * c) + s * c := by rw [hcs.eq]
      _ = 0 := neg_add_cancel (s * c)
  rw [hcancel]
  noncomm_ring

end NonCommRingTwoModeFlow

variable {R : Type*} [CommRing R]

/-- Concrete coordinates of `zornTracelessExp`. -/
theorem zornTracelessExp_coordinates (c s α : R) (v w : ZornVec3 R) :
    zornTracelessExp c s α v w =
      ⟨c + s * α, (fun i => s * v i), (fun i => s * w i), c - s * α⟩ :=
  (zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 α v w).1

/-- Two-mode Cayley--Hamilton multiplication in a common generator. -/
theorem zornTracelessExp_mul
    (c₁ s₁ c₂ s₂ α : R) (v w : ZornVec3 R) :
    zornTracelessExp c₁ s₁ α v w * zornTracelessExp c₂ s₂ α v w =
      zornTracelessExp
        (c₁ * c₂ + s₁ * s₂ * zornTracelessCasimir α v w)
        (c₁ * s₂ + s₁ * c₂) α v w :=
  (zornTracelessExp_coords_casimir_norm_and_group_law 0 0 c₁ s₁ c₂ s₂ α v w).2.2.1

/-- Inverse candidate and its scalar norm obstruction; no invertibility is assumed. -/
theorem zornTracelessExp_mul_opposite
    (c s α : R) (v w : ZornVec3 R) :
    zornTracelessExp c s α v w * zornTracelessExp c (-s) α v w =
      (c * c - s * s * zornTracelessCasimir α v w) •
        (one : ZornVectorMatrix R) :=
  (zornTracelessExp_coords_casimir_norm_and_group_law c s 0 0 0 0 α v w).2.2.2

end InfoGeometry.Algebra.ZornVectorMatrix
