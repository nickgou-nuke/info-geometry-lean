/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.GoodBadGibbs

/-!
# Normalized finite good-fit volume

The effective good count is normalized by the finite data cardinality. The
result is a bounded order parameter for temperature scans and diagnostics;
the formalization makes no thermodynamic-limit claim.
-/

namespace InfoGeometry.Inference

open scoped BigOperators

variable {Data : Type*} [Fintype Data] [Nonempty Data]

noncomputable def effectiveGoodFraction
    (E : GoodBadEnergy (Data := Data)) (εg εb : ℝ) : ℝ :=
  effectiveGoodCount E εg εb / Fintype.card Data

theorem effectiveGoodFraction_pos
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) :
    0 < effectiveGoodFraction E εg εb := by
  unfold effectiveGoodFraction
  apply div_pos
  · exact effectiveGoodCount_pos E hεg hεb hg hb
  · exact_mod_cast Fintype.card_pos

theorem effectiveGoodFraction_le_one
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) :
    effectiveGoodFraction E εg εb ≤ 1 := by
  unfold effectiveGoodFraction
  apply (div_le_iff₀ (show (0 : ℝ) < Fintype.card Data by exact_mod_cast Fintype.card_pos)).2
  simpa using (effectiveGoodCount_le_card E hεg hεb hg hb)

end InfoGeometry.Inference
