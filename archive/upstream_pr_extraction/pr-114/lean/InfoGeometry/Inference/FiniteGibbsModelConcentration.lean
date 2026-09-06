/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsModelFamily

/-!
# Quantitative concentration of finite Gibbs model volume

An energy gap separates a non-minimizing model from a reference model by an
explicit Boltzmann factor.  Averaging the pointwise estimate over observations
gives a model-volume concentration bound, without making an unproved
zero-temperature limit claim.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators

variable {ModelId Data : Type*} [Fintype ModelId] [Nonempty ModelId]
  [Fintype Data] [Nonempty Data]

/-- A uniform energy gap bounds the volume assigned to the separated model. -/
theorem modelVolume_le_prior_ratio_mul_exp_neg_gap
    (F : ModelFamily (ModelId := ModelId) (Data := Data))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (m m₀ : ModelId)
    (hgap : ∀ i : Data, F.energy m₀ i + δ ≤ F.energy m i) :
    modelVolume F ε m ≤
      (F.prior m / F.prior m₀) * Real.exp (-δ / ε) := by
  have hratio : ∀ i : Data,
      responsibility F ε m i / responsibility F ε m₀ i ≤
        (F.prior m / F.prior m₀) * Real.exp (-δ / ε) := by
    intro i
    exact responsibility_ratio_le_prior_ratio_mul_exp_neg_gap F hε m m₀ i
      (hgap i)
  have hresp₀_le_one : ∀ i : Data, responsibility F ε m₀ i ≤ 1 := by
    intro i
    have hsingle : responsibility F ε m₀ i ≤
        ∑ n : ModelId, responsibility F ε n i := by
      exact Finset.single_le_sum
        (fun n hn => (responsibility_nonneg F ε n i))
        (Finset.mem_univ m₀)
    simpa [responsibilities_sum_one] using hsingle
  have hfactor_nonneg : 0 ≤
      (F.prior m / F.prior m₀) * Real.exp (-δ / ε) := by
    have hexp_interval : 0 ≤ Real.exp (-δ / ε) ∧
        Real.exp (-δ / ε) < 1 := by
      constructor
      · exact (Real.exp_pos _).le
      · apply Real.exp_lt_one_iff.mpr
        have hneg : -(δ / ε) < 0 := neg_lt_zero.mpr (div_pos hδ hε)
        convert hneg using 1 <;> ring
    exact mul_nonneg
      (div_nonneg (F.prior_pos m).le (F.prior_pos m₀).le)
      hexp_interval.1
  have hpointwise : ∀ i : Data,
      responsibility F ε m i ≤
        (F.prior m / F.prior m₀) * Real.exp (-δ / ε) := by
    intro i
    have hmul := (div_le_iff₀ (responsibility_pos F ε m₀ i)).mp (hratio i)
    have hupper := mul_le_mul_of_nonneg_left (hresp₀_le_one i) hfactor_nonneg
    have hupper' :
        (F.prior m / F.prior m₀) * Real.exp (-δ / ε) *
          responsibility F ε m₀ i ≤
          (F.prior m / F.prior m₀) * Real.exp (-δ / ε) := by
      simpa using hupper
    exact hmul.trans hupper'
  unfold modelVolume
  apply (div_le_iff₀ (show (0 : ℝ) < Fintype.card Data by
    exact_mod_cast Fintype.card_pos)).2
  calc
    ∑ i : Data, responsibility F ε m i ≤
        ∑ _i : Data,
          (F.prior m / F.prior m₀) * Real.exp (-δ / ε) := by
      exact Finset.sum_le_sum (fun i hi => hpointwise i)
    _ = (F.prior m / F.prior m₀) * Real.exp (-δ / ε) *
        (Fintype.card Data : ℝ) := by
      simp [nsmul_eq_mul]
      ring

end InfoGeometry.Inference.FiniteGibbs
