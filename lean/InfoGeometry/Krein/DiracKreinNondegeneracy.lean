/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DiracKreinFisherBridge
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! Exact recovery and radical laws for the existing doubled neutral form.
The neutral difference form and doubled sum form remain distinct. -/

noncomputable section

namespace InfoGeometry.Krein.DiracKreinFisherBridge

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Twisting the neutral form back recovers the doubled sum form. -/
@[simp] theorem diracKreinBilin_spectral_epsilon_right
    (G : LinearMap.BilinForm ℝ E) (u v : DoubledSpace E) :
    diracKreinBilin G u (spectral_epsilon v) = doubledPositiveBilin G u v := by
  simp [diracKreinBilin_apply, spectral_epsilon, doubledPositiveBilin]

/-- The first-sheet inclusion preserves the original bilinear form exactly. -/
@[simp] theorem diracKreinBilin_first_sheet
    (G : LinearMap.BilinForm ℝ E) (x y : E) :
    diracKreinBilin G (to_doubled x 0) (to_doubled y 0) = G x y := by
  simp

/-- The left radical is the product of the two original left radicals. -/
theorem diracKreinBilin_left_radical_iff
    (G : LinearMap.BilinForm ℝ E) (u : DoubledSpace E) :
    (∀ v, diracKreinBilin G u v = 0) ↔
      (∀ y, G (WithLp.fst u) y = 0) ∧ (∀ y, G (WithLp.snd u) y = 0) := by
  constructor
  · intro h
    constructor
    · intro y
      simpa using h (to_doubled y 0)
    · intro y
      simpa using h (to_doubled 0 y)
  · rintro ⟨h₁, h₂⟩ v
    simp [h₁, h₂]

/-- The right radical is the product of the two original right radicals. -/
theorem diracKreinBilin_right_radical_iff
    (G : LinearMap.BilinForm ℝ E) (v : DoubledSpace E) :
    (∀ u, diracKreinBilin G u v = 0) ↔
      (∀ x, G x (WithLp.fst v) = 0) ∧ (∀ x, G x (WithLp.snd v) = 0) := by
  constructor
  · intro h
    constructor
    · intro x
      simpa using h (to_doubled x 0)
    · intro x
      simpa using h (to_doubled 0 x)
  · rintro ⟨h₁, h₂⟩ u
    simp [h₁, h₂]

/-- Doubling preserves and reflects two-sided nondegeneracy, even in infinite
dimension and without assuming symmetry of the original form. -/
theorem diracKreinBilin_nondegenerate_iff (G : LinearMap.BilinForm ℝ E) :
    (diracKreinBilin G).Nondegenerate ↔ G.Nondegenerate := by
  constructor
  · intro h
    constructor
    · intro x hx
      have hz := h.1 (to_doubled x 0) (by
        intro v
        simp [hx])
      simpa using congrArg WithLp.fst hz
    · intro y hy
      have hz := h.2 (to_doubled y 0) (by
        intro u
        simp [hy])
      simpa using congrArg WithLp.fst hz
  · intro h
    constructor
    · intro u hu
      obtain ⟨h₁, h₂⟩ := (diracKreinBilin_left_radical_iff G u).mp hu
      apply DoubledSpace.ext
      · simpa using h.1 _ h₁
      · simpa using h.1 _ h₂
    · intro v hv
      obtain ⟨h₁, h₂⟩ := (diracKreinBilin_right_radical_iff G v).mp hv
      apply DoubledSpace.ext
      · simpa using h.2 _ h₁
      · simpa using h.2 _ h₂

end InfoGeometry.Krein.DiracKreinFisherBridge
