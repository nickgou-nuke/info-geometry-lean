/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsModelVolumeMarginal
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

end InfoGeometry.Inference.FiniteGibbs
