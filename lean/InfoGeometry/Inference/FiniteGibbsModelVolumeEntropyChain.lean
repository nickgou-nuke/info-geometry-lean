/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsModelVolumeMarginal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.FiniteGibbsThermodynamicIdentity

/-!
# Entropy chain rule for responsibility coarse-graining

The joint model/observation volume has uniform observation marginal.  Its
entropy therefore decomposes into the entropy of the observation volume plus
the average conditional responsibility entropy.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators

variable {ModelId Data : Type*} [Fintype ModelId] [Nonempty ModelId]
  [Fintype Data] [Nonempty Data]

/-- Entropy of the responsibility simplex at one observation. -/
noncomputable def responsibilityEntropy
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) (i : Data) : ℝ :=
  -∑ m : ModelId,
      responsibility F ε m i * Real.log (responsibility F ε m i)

/-- Entropy of the normalized joint model/observation volume. -/
noncomputable def jointModelDataEntropy
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    (ε : ℝ) : ℝ :=
  -∑ m : ModelId, ∑ i : Data,
      jointModelDataVolume F ε m i * Real.log (jointModelDataVolume F ε m i)

/-- Joint responsibility volume entropy obeys the finite entropy chain rule. -/
theorem jointModelDataEntropy_eq_log_card_add_average_responsibilityEntropy
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    jointModelDataEntropy F ε =
      Real.log (Fintype.card Data) +
        (1 / Fintype.card Data : ℝ) *
          ∑ i : Data, responsibilityEntropy F ε i := by
  let n : ℝ := Fintype.card Data
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos
  have hlog : ∀ m : ModelId, ∀ i : Data,
      Real.log (jointModelDataVolume F ε m i) =
        Real.log (responsibility F ε m i) - Real.log n := by
    intro m i
    unfold jointModelDataVolume
    rw [Real.log_div (ne_of_gt (responsibility_pos F ε m i)) (ne_of_gt hn)]
  unfold jointModelDataEntropy responsibilityEntropy
  dsimp [n] at hn hlog ⊢
  simp_rw [hlog, jointModelDataVolume, mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have hresp : ∀ i : Data,
      ∑ m : ModelId, responsibility F ε m i = 1 :=
    fun i => responsibilities_sum_one F ε i
  have harea :
      ∑ i : Data, ∑ m : ModelId,
          responsibility F ε m i / Fintype.card Data *
            Real.log (responsibility F ε m i) =
        (1 / Fintype.card Data : ℝ) *
          ∑ i : Data, ∑ m : ModelId,
            responsibility F ε m i * Real.log (responsibility F ε m i) := by
    simp_rw [div_eq_mul_inv]
    calc
      ∑ i : Data, ∑ m : ModelId,
          responsibility F ε m i * (Fintype.card Data : ℝ)⁻¹ *
            Real.log (responsibility F ε m i) =
          ∑ i : Data,
            (∑ m : ModelId,
              responsibility F ε m i * Real.log (responsibility F ε m i)) *
              (Fintype.card Data : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ∑ m : ModelId,
              responsibility F ε m i * (Fintype.card Data : ℝ)⁻¹ *
                Real.log (responsibility F ε m i) =
              ∑ m : ModelId,
                (responsibility F ε m i *
                  Real.log (responsibility F ε m i)) *
                  (Fintype.card Data : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ = (∑ m : ModelId,
                responsibility F ε m i *
                  Real.log (responsibility F ε m i)) *
                (Fintype.card Data : ℝ)⁻¹ := by
            exact (Finset.sum_mul
              (s := (Finset.univ : Finset ModelId))
              (f := fun m : ModelId =>
                responsibility F ε m i * Real.log (responsibility F ε m i))
              (a := (Fintype.card Data : ℝ)⁻¹)).symm
      _ = (∑ i : Data, ∑ m : ModelId,
            responsibility F ε m i * Real.log (responsibility F ε m i)) *
            (Fintype.card Data : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
      _ = (1 / Fintype.card Data : ℝ) *
          ∑ i : Data, ∑ m : ModelId,
            responsibility F ε m i * Real.log (responsibility F ε m i) := by
        ring
  have hbackground :
      ∑ m : ModelId, ∑ i : Data,
          responsibility F ε m i / Fintype.card Data *
            Real.log (Fintype.card Data) =
        Real.log (Fintype.card Data) := by
    calc
      ∑ m : ModelId, ∑ i : Data,
          responsibility F ε m i / Fintype.card Data *
            Real.log (Fintype.card Data) =
          ∑ i : Data, ∑ m : ModelId,
            responsibility F ε m i / Fintype.card Data *
              Real.log (Fintype.card Data) := by
        rw [Finset.sum_comm]
      _ = ∑ i : Data,
            ((∑ m : ModelId, responsibility F ε m i) /
              Fintype.card Data) * Real.log (Fintype.card Data) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          ∑ m : ModelId,
              responsibility F ε m i / Fintype.card Data *
                Real.log (Fintype.card Data) =
              (∑ m : ModelId,
                responsibility F ε m i / Fintype.card Data) *
                Real.log (Fintype.card Data) := by
            exact (Finset.sum_mul
              (s := (Finset.univ : Finset ModelId))
              (f := fun m : ModelId =>
                responsibility F ε m i / Fintype.card Data)
              (a := Real.log (Fintype.card Data))).symm
          _ = ((∑ m : ModelId, responsibility F ε m i) /
                Fintype.card Data) * Real.log (Fintype.card Data) := by
            congr 1
            exact (Finset.sum_div
              (s := (Finset.univ : Finset ModelId))
              (f := fun m : ModelId => responsibility F ε m i)
              (a := Fintype.card Data)).symm
      _ = ∑ i : Data,
            (1 / Fintype.card Data : ℝ) * Real.log (Fintype.card Data) := by
        simp_rw [hresp]
      _ = Real.log (Fintype.card Data) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp [nsmul_eq_mul]

  rw [harea, hbackground]
  rw [Finset.sum_neg_distrib]
  ring

/-- The joint entropy dominates the observation-volume entropy. -/
theorem log_card_data_le_jointModelDataEntropy
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    Real.log (Fintype.card Data) ≤ jointModelDataEntropy F ε := by
  rw [jointModelDataEntropy_eq_log_card_add_average_responsibilityEntropy]
  have hcond : ∀ i : Data, 0 ≤ responsibilityEntropy F ε i := by
    intro i
    unfold responsibilityEntropy
    exact entropyOf_nonneg (Data := ModelId)
      (fun m => responsibility F ε m i)
      (fun m => responsibility_pos F ε m i)
      (responsibilities_sum_one F ε i)
  have hsum : 0 ≤ ∑ i : Data, responsibilityEntropy F ε i :=
    Finset.sum_nonneg (fun i hi => hcond i)
  have hcard : 0 ≤ (1 / Fintype.card Data : ℝ) := by
    positivity
  have havg : 0 ≤ (1 / Fintype.card Data : ℝ) *
      ∑ i : Data, responsibilityEntropy F ε i :=
    mul_nonneg hcard hsum
  linarith

/-- The joint entropy is bounded by the log-cardinality of both finite axes. -/
theorem jointModelDataEntropy_le_log_card_add_log_card
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    jointModelDataEntropy F ε ≤
      Real.log (Fintype.card Data) + Real.log (Fintype.card ModelId) := by
  rw [jointModelDataEntropy_eq_log_card_add_average_responsibilityEntropy]
  have hcond : ∀ i : Data,
      responsibilityEntropy F ε i ≤ Real.log (Fintype.card ModelId) := by
    intro i
    unfold responsibilityEntropy
    exact entropyOf_le_log_card (Data := ModelId)
      (fun m => responsibility F ε m i)
      (fun m => responsibility_pos F ε m i)
      (responsibilities_sum_one F ε i)
  have hsum : ∑ i : Data, responsibilityEntropy F ε i ≤
      ∑ i : Data, Real.log (Fintype.card ModelId) :=
    Finset.sum_le_sum (fun i hi => hcond i)
  have hcard : 0 ≤ (1 / Fintype.card Data : ℝ) := by
    positivity
  have havg : (1 / Fintype.card Data : ℝ) *
      ∑ i : Data, responsibilityEntropy F ε i ≤
      (1 / Fintype.card Data : ℝ) *
        ∑ i : Data, Real.log (Fintype.card ModelId) :=
    mul_le_mul_of_nonneg_left hsum hcard
  have hconstant :
      (1 / Fintype.card Data : ℝ) *
        ∑ i : Data, Real.log (Fintype.card ModelId) =
      Real.log (Fintype.card ModelId) := by
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]
  rw [hconstant] at havg
  linarith

/-- The joint upper entropy bound is attained exactly by uniform responsibilities. -/
theorem jointModelDataEntropy_eq_log_card_add_log_card_iff_uniform
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    jointModelDataEntropy F ε =
        Real.log (Fintype.card Data) + Real.log (Fintype.card ModelId) ↔
      ∀ i : Data, ∀ m : ModelId,
        responsibility F ε m i = 1 / (Fintype.card ModelId : ℝ) := by
  have hD : 0 < (Fintype.card Data : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hM : 0 < (Fintype.card ModelId : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcond : ∀ i : Data,
      responsibilityEntropy F ε i ≤ Real.log (Fintype.card ModelId) := by
    intro i
    unfold responsibilityEntropy
    exact entropyOf_le_log_card (Data := ModelId)
      (fun m => responsibility F ε m i)
      (fun m => responsibility_pos F ε m i)
      (responsibilities_sum_one F ε i)
  constructor
  · intro h
    have hsum : ∑ i : Data, responsibilityEntropy F ε i =
        (Fintype.card Data : ℝ) * Real.log (Fintype.card ModelId) := by
      have hchain :=
        jointModelDataEntropy_eq_log_card_add_average_responsibilityEntropy F ε
      have havg : (1 / Fintype.card Data : ℝ) *
          ∑ i : Data, responsibilityEntropy F ε i =
          Real.log (Fintype.card ModelId) := by
        rw [h] at hchain
        linarith
      calc
        ∑ i : Data, responsibilityEntropy F ε i =
            (Fintype.card Data : ℝ) *
              ((1 / Fintype.card Data : ℝ) *
                ∑ i : Data, responsibilityEntropy F ε i) := by
          field_simp [Fintype.card_ne_zero]
        _ = (Fintype.card Data : ℝ) *
            Real.log (Fintype.card ModelId) := by rw [havg]
    have hdef_nonneg : ∀ i : Data,
        0 ≤ Real.log (Fintype.card ModelId) - responsibilityEntropy F ε i := by
      intro i
      linarith [hcond i]
    have hdef_sum : ∑ i : Data,
        (Real.log (Fintype.card ModelId) - responsibilityEntropy F ε i) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul]
      linarith
    have hdef_zero : ∀ i : Data,
        Real.log (Fintype.card ModelId) - responsibilityEntropy F ε i = 0 := by
      intro i
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => hdef_nonneg j)).mp hdef_sum
      exact hall i (Finset.mem_univ i)
    intro i m
    have hi : responsibilityEntropy F ε i =
        Real.log (Fintype.card ModelId) := by linarith [hdef_zero i]
    change entropyOf (fun m : ModelId => responsibility F ε m i) =
      Real.log (Fintype.card ModelId) at hi
    have huniform := (entropyOf_eq_log_card_iff_uniform
      (Data := ModelId) (fun m : ModelId => responsibility F ε m i)
      (fun m => responsibility_pos F ε m i)
      (responsibilities_sum_one F ε i)).mp hi
    exact huniform m
  · intro huniform
    rw [jointModelDataEntropy_eq_log_card_add_average_responsibilityEntropy]
    have hcond_eq : ∀ i : Data,
        responsibilityEntropy F ε i = Real.log (Fintype.card ModelId) := by
      intro i
      change entropyOf (fun m : ModelId => responsibility F ε m i) =
        Real.log (Fintype.card ModelId)
      exact (entropyOf_eq_log_card_iff_uniform
        (Data := ModelId) (fun m : ModelId => responsibility F ε m i)
        (fun m => responsibility_pos F ε m i)
        (responsibilities_sum_one F ε i)).mpr (fun m => huniform i m)
    simp_rw [hcond_eq]
    rw [Finset.sum_const, Finset.card_univ]
    simp [nsmul_eq_mul]

/-- The lower entropy bound is attained exactly when every conditional entropy vanishes. -/
theorem jointModelDataEntropy_eq_log_card_data_iff_conditional_entropy_zero
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    jointModelDataEntropy F ε = Real.log (Fintype.card Data) ↔
      ∀ i : Data, responsibilityEntropy F ε i = 0 := by
  have hcond : ∀ i : Data, 0 ≤ responsibilityEntropy F ε i := by
    intro i
    unfold responsibilityEntropy
    exact entropyOf_nonneg (Data := ModelId)
      (fun m => responsibility F ε m i)
      (fun m => responsibility_pos F ε m i)
      (responsibilities_sum_one F ε i)
  constructor
  · intro h
    have hchain :=
      jointModelDataEntropy_eq_log_card_add_average_responsibilityEntropy F ε
    have havg : (1 / Fintype.card Data : ℝ) *
        ∑ i : Data, responsibilityEntropy F ε i = 0 := by
      rw [h] at hchain
      linarith
    have hsum : ∑ i : Data, responsibilityEntropy F ε i = 0 := by
      exact (mul_eq_zero.mp havg).resolve_left (by positivity)
    intro i
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => hcond j)).mp hsum
    exact hall i (Finset.mem_univ i)
  · intro hz
    rw [jointModelDataEntropy_eq_log_card_add_average_responsibilityEntropy]
    have hsum : ∑ i : Data, responsibilityEntropy F ε i = 0 := by
      simp_rw [hz]
      simp
    rw [hsum]
    ring

/-- Positive-temperature Gibbs responsibilities have positive entropy for a
nontrivial finite model family. -/
theorem responsibilityEntropy_pos_of_one_lt_model_card
    (hcard : 1 < Fintype.card ModelId)
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) (i : Data) :
    0 < responsibilityEntropy F ε i := by
  have hq_pos : ∀ m : ModelId, 0 < responsibility F ε m i :=
    fun m => responsibility_pos F ε m i
  have hq_sum : ∑ m : ModelId, responsibility F ε m i = 1 :=
    responsibilities_sum_one F ε i
  have hq_le_one : ∀ m : ModelId, responsibility F ε m i ≤ 1 := by
    intro m
    have hsingle : responsibility F ε m i ≤
        ∑ n : ModelId, responsibility F ε n i := by
      exact Finset.single_le_sum (fun n hn => (hq_pos n).le)
        (Finset.mem_univ m)
    simpa [hq_sum] using hsingle
  have hterm_nonneg : ∀ m : ModelId,
      0 ≤ -(responsibility F ε m i *
        Real.log (responsibility F ε m i)) := by
    intro m
    have hlog := Real.log_le_sub_one_of_pos (hq_pos m)
    have hmul := mul_le_mul_of_nonneg_left hlog (hq_pos m).le
    have hquad : responsibility F ε m i *
        (responsibility F ε m i - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hq_pos m).le
        (sub_nonpos.mpr (hq_le_one m))
    linarith
  obtain ⟨m₀⟩ := ‹Nonempty ModelId›
  obtain ⟨m₁, hm₁⟩ := Fintype.exists_ne_of_one_lt_card hcard m₀
  have hstrict : responsibility F ε m₀ i < 1 := by
    have hlt := Finset.single_lt_sum
      (s := (Finset.univ : Finset ModelId)) hm₁
      (Finset.mem_univ m₀) (Finset.mem_univ m₁) (hq_pos m₁)
      (fun m hm hne => (hq_pos m).le)
    simpa [hq_sum] using hlt
  have hlog_strict : Real.log (responsibility F ε m₀ i) < 0 :=
    Real.log_neg (hq_pos m₀) hstrict
  have hterm_strict : 0 < -(responsibility F ε m₀ i *
      Real.log (responsibility F ε m₀ i)) := by
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (hq_pos m₀) hlog_strict)
  unfold responsibilityEntropy
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_pos' (fun m hm => hterm_nonneg m)
    ⟨m₀, Finset.mem_univ m₀, hterm_strict⟩

/-- A nontrivial finite-temperature model family contributes strictly positive
conditional volume to the joint entropy. -/
theorem jointModelDataEntropy_gt_log_card_data_of_one_lt_model_card
    (hcard : 1 < Fintype.card ModelId)
    (F : ModelFamily (ModelId := ModelId) (Data := Data)) (ε : ℝ) :
    Real.log (Fintype.card Data) < jointModelDataEntropy F ε := by
  rw [jointModelDataEntropy_eq_log_card_add_average_responsibilityEntropy]
  have hsum : 0 < ∑ i : Data, responsibilityEntropy F ε i := by
    exact Finset.sum_pos (fun i hi =>
      responsibilityEntropy_pos_of_one_lt_model_card hcard F ε i)
      Finset.univ_nonempty
  have hfactor : 0 < (1 / Fintype.card Data : ℝ) := by
    positivity
  have havg : 0 < (1 / Fintype.card Data : ℝ) *
      ∑ i : Data, responsibilityEntropy F ε i :=
    mul_pos hfactor hsum
  linarith

end InfoGeometry.Inference.FiniteGibbs
