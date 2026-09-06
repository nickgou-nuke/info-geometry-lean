/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite good/bad Gibbs responsibilities

This is an explicit two-state contamination layer. Its responsibilities are
posterior good-state probabilities only because the good and bad energies and
their prior masses are supplied separately.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data]

structure GoodBadEnergy where
  goodEnergy : Data → ℝ
  badEnergy : Data → ℝ
  goodPrior : Data → ℝ
  badPrior : Data → ℝ

noncomputable def goodBadPartition
    (E : GoodBadEnergy (Data := Data))
    (εg εb : ℝ) (i : Data) : ℝ :=
  E.goodPrior i * Real.exp (-E.goodEnergy i / εg) +
    E.badPrior i * Real.exp (-E.badEnergy i / εb)

noncomputable def goodResponsibility
    (E : GoodBadEnergy (Data := Data))
    (εg εb : ℝ) (i : Data) : ℝ :=
  (E.goodPrior i * Real.exp (-E.goodEnergy i / εg)) /
    goodBadPartition E εg εb i

noncomputable def badResponsibility
    (E : GoodBadEnergy (Data := Data))
    (εg εb : ℝ) (i : Data) : ℝ :=
  (E.badPrior i * Real.exp (-E.badEnergy i / εb)) /
    goodBadPartition E εg εb i

theorem goodBadPartition_pos
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) (i : Data) :
    0 < goodBadPartition E εg εb i := by
  unfold goodBadPartition
  exact add_pos (mul_pos (hg i) (Real.exp_pos _))
    (mul_pos (hb i) (Real.exp_pos _))

theorem goodResponsibility_nonneg
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) (i : Data) :
    0 ≤ goodResponsibility E εg εb i := by
  unfold goodResponsibility
  exact div_nonneg (le_of_lt (mul_pos (hg i) (Real.exp_pos _)))
    (le_of_lt (goodBadPartition_pos E hεg hεb hg hb i))

theorem badResponsibility_nonneg
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) (i : Data) :
    0 ≤ badResponsibility E εg εb i := by
  unfold badResponsibility
  exact div_nonneg (le_of_lt (mul_pos (hb i) (Real.exp_pos _)))
    (le_of_lt (goodBadPartition_pos E hεg hεb hg hb i))

theorem goodResponsibility_le_one
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) (i : Data) :
    goodResponsibility E εg εb i ≤ 1 := by
  unfold goodResponsibility goodBadPartition
  apply (div_le_iff₀ (goodBadPartition_pos E hεg hεb hg hb i)).2
  simp only [one_mul]
  have hbad : 0 ≤ E.badPrior i * Real.exp (-E.badEnergy i / εb) :=
    (mul_pos (hb i) (Real.exp_pos _)).le
  simpa [goodBadPartition] using
    (le_add_of_nonneg_right (a := E.goodPrior i *
      Real.exp (-E.goodEnergy i / εg)) hbad)

theorem goodBadResponsibility_sum_one
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) (i : Data) :
    goodResponsibility E εg εb i + badResponsibility E εg εb i = 1 := by
  unfold goodResponsibility badResponsibility goodBadPartition
  rw [← add_div]
  exact div_self (ne_of_gt (goodBadPartition_pos E hεg hεb hg hb i))

noncomputable def effectiveGoodCount
    (E : GoodBadEnergy (Data := Data)) (εg εb : ℝ) : ℝ :=
  ∑ i : Data, goodResponsibility E εg εb i

theorem effectiveGoodCount_nonneg
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) :
    0 ≤ effectiveGoodCount E εg εb := by
  unfold effectiveGoodCount
  exact Finset.sum_nonneg (fun i hi => goodResponsibility_nonneg E hεg hεb hg hb i)

theorem effectiveGoodCount_pos
    [Nonempty Data]
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) :
    0 < effectiveGoodCount E εg εb := by
  unfold effectiveGoodCount
  exact Finset.sum_pos
    (fun i hi => div_pos (mul_pos (hg i) (Real.exp_pos _))
      (goodBadPartition_pos E hεg hεb hg hb i))
    Finset.univ_nonempty

theorem effectiveGoodCount_le_card
    (E : GoodBadEnergy (Data := Data))
    {εg εb : ℝ} (hεg : 0 < εg) (hεb : 0 < εb)
    (hg : ∀ i, 0 < E.goodPrior i)
    (hb : ∀ i, 0 < E.badPrior i) :
    effectiveGoodCount E εg εb ≤ Fintype.card Data := by
  unfold effectiveGoodCount
  calc
    ∑ i : Data, goodResponsibility E εg εb i
        ≤ ∑ _i : Data, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun i hi =>
            goodResponsibility_le_one E hεg hεb hg hb i)
    _ = Fintype.card Data := by simp

end InfoGeometry.Inference
