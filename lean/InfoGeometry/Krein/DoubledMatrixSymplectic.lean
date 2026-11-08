/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DoubleRealKreinShearDefect
import InfoGeometry.Canonical.ChiralBoundarySymplecticBridge

/-! The native doubled matrix action preserves the existing chiral alternating
form when its determinant is one. This does not change the diagonal Krein form
or assert that a nonzero shear is a Krein isometry. -/
noncomputable section
namespace InfoGeometry.Krein.DoubledMatrixSymplectic

open InfoGeometry.Krein
open DoubledSpaceMatrixClockBridge DoubledSpaceRealKANBridge
open InfoGeometry.Canonical.ChiralBoundarySymplectic.ChiralDoubled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pull back the existing product-space form along the native `WithLp` coordinates. -/
theorem matrixAction_symplectic_det (A : Matrix (Fin 2) (Fin 2) ℝ)
    (X Y : DoubledSpace E) :
    symplecticForm (WithLp.ofLp (ρclock A X)) (WithLp.ofLp (ρclock A Y)) =
      A.det * symplecticForm (WithLp.ofLp X) (WithLp.ofLp Y) := by
  simp [symplecticForm, ρclock, matrixAction, to_doubled, Matrix.det_fin_two,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm]
  ring

theorem matrixAction_preserves_symplectic (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.det = 1) (X Y : DoubledSpace E) :
    symplecticForm (WithLp.ofLp (ρclock A X)) (WithLp.ofLp (ρclock A Y)) =
      symplecticForm (WithLp.ofLp X) (WithLp.ofLp Y) := by
  rw [matrixAction_symplectic_det, hA, one_mul]

/-- The original upper shear is symplectic for every real parameter. -/
theorem componentNReal_preserves_symplectic (t : ℝ) (X Y : DoubledSpace E) :
    symplecticForm (WithLp.ofLp (ρclock (componentNReal t) X))
      (WithLp.ofLp (ρclock (componentNReal t) Y)) =
        symplecticForm (WithLp.ofLp X) (WithLp.ofLp Y) := by
  apply matrixAction_preserves_symplectic
  simp [componentNReal, Matrix.det_fin_two]

/-- On a nontrivial coefficient space, determinant one is also necessary. -/
theorem matrixAction_preserves_symplectic_iff [Nontrivial E]
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ X Y : DoubledSpace E,
      symplecticForm (WithLp.ofLp (ρclock A X)) (WithLp.ofLp (ρclock A Y)) =
        symplecticForm (WithLp.ofLp X) (WithLp.ofLp Y)) ↔ A.det = 1 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hp := h (to_doubled x 0) (to_doubled 0 x)
    rw [matrixAction_symplectic_det] at hp
    have heq : A.det * inner ℝ x x = 1 * inner ℝ x x := by
      simpa [symplecticForm, to_doubled] using hp
    exact mul_right_cancel₀ (ne_of_gt (real_inner_self_pos.mpr hx)) heq
  · intro h X Y
    exact matrixAction_preserves_symplectic A h X Y

end InfoGeometry.Krein.DoubledMatrixSymplectic
