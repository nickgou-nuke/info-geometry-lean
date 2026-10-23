/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.DiracKreinNondegeneracy

/-! Positivity belongs to the doubled sum form; the neutral form has opposite
sheet signs. No symmetry or finite dimension assumption is used. -/

noncomputable section

namespace InfoGeometry.Krein.DiracKreinFisherBridge

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The doubled sum is nonnegative exactly when the original form is. -/
theorem doubledPositiveBilin_isNonneg_iff (G : LinearMap.BilinForm ℝ E) :
    (doubledPositiveBilin G).IsNonneg ↔ G.IsNonneg := by
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    simpa [doubledPositiveBilin] using h.nonneg (to_doubled x 0)
  · intro h
    refine ⟨fun u => ?_⟩
    exact add_nonneg (h.nonneg (WithLp.fst u)) (h.nonneg (WithLp.snd u))

omit [CompleteSpace E] in
/-- Under nonnegativity, a zero doubled diagonal has two zero component diagonals. -/
theorem doubledPositiveBilin_self_eq_zero_iff
    (G : LinearMap.BilinForm ℝ E) (hG : G.IsNonneg) (u : DoubledSpace E) :
    doubledPositiveBilin G u u = 0 ↔
      G (WithLp.fst u) (WithLp.fst u) = 0 ∧
      G (WithLp.snd u) (WithLp.snd u) = 0 := by
  change G (WithLp.fst u) (WithLp.fst u) + G (WithLp.snd u) (WithLp.snd u) = 0 ↔ _
  exact add_eq_zero_iff_of_nonneg (hG.nonneg (WithLp.fst u)) (hG.nonneg (WithLp.snd u))

omit [CompleteSpace E] in
/-- Strict diagonal positivity is preserved and reflected by doubling. -/
theorem doubledPositiveBilin_strict_pos_iff (G : LinearMap.BilinForm ℝ E) :
    (∀ u : DoubledSpace E, u ≠ 0 → 0 < doubledPositiveBilin G u u) ↔
      (∀ x : E, x ≠ 0 → 0 < G x x) := by
  constructor
  · intro h x hx
    have hu : (to_doubled x 0 : DoubledSpace E) ≠ 0 := by
      intro hz
      apply hx
      simpa using congrArg WithLp.fst hz
    simpa [doubledPositiveBilin] using h (to_doubled x 0) hu
  · intro h u hu
    have hn : ∀ x : E, 0 ≤ G x x := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · exact le_of_lt (h x hx)
    change 0 < G (WithLp.fst u) (WithLp.fst u) + G (WithLp.snd u) (WithLp.snd u)
    by_cases hf : WithLp.fst u = 0
    · have hs : WithLp.snd u ≠ 0 := by
        intro hs
        apply hu
        apply DoubledSpace.ext <;> simpa
      simpa [hf] using h (WithLp.snd u) hs
    · exact add_pos_of_pos_of_nonneg (h (WithLp.fst u) hf) (hn (WithLp.snd u))

/-- The second-sheet inclusion reverses the original bilinear form. -/
@[simp] theorem diracKreinBilin_second_sheet
    (G : LinearMap.BilinForm ℝ E) (x y : E) :
    diracKreinBilin G (to_doubled 0 x) (to_doubled 0 y) = -G x y := by
  simp

/-- A strictly positive form on a nontrivial carrier gives actual opposite-sign
vectors for its neutral double. -/
theorem diracKreinBilin_has_opposite_signs [Nontrivial E]
    (G : LinearMap.BilinForm ℝ E) (hG : ∀ x : E, x ≠ 0 → 0 < G x x) :
    ∃ u v : DoubledSpace E,
      0 < diracKreinBilin G u u ∧ diracKreinBilin G v v < 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  refine ⟨to_doubled x 0, to_doubled 0 x, ?_, ?_⟩
  · simpa using hG x hx
  · simpa using neg_neg_of_pos (hG x hx)

end InfoGeometry.Krein.DiracKreinFisherBridge
