import InfoGeometry.Detector.ApollonianBalanceParabola
import InfoGeometry.Physics.FermionicAndreevReflection
import InfoGeometry.Algebra.CyclotomicPhaseReadout
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Finite amplitude and conditional counting identities

The counting dependency is conservation → normalization → equipartition → entropy.
The amplitude and cyclotomic branches are independent. No scattering law equating
these models, spectral lower bound, or winding number of a continuous loop is
asserted. Equal conditional counts do not imply one bit per incident decay.
-/

noncomputable section

namespace InfoGeometry.Nuclear.AndreevCascadeInterferometer

open DetectorGeometry.ApollonianBalanceParabola
open InfoGeometry.Physics.FermionicAndreevReflection
open InfoGeometry.Algebra.CyclotomicPhaseReadout

theorem count_conservation (intensity coupling efficiency : ℝ) :
    singleObserved intensity coupling efficiency + coincidenceRate intensity coupling efficiency =
      intensity * efficiency := by
  unfold singleObserved coincidenceRate
  ring

theorem conditional_single_fraction (intensity coupling efficiency : ℝ)
    (htotal : intensity * efficiency ≠ 0) :
    singleObserved intensity coupling efficiency / (intensity * efficiency) =
      1 - coupling * efficiency := by
  unfold singleObserved
  exact mul_div_cancel_left₀ _ htotal

theorem conditional_pair_fraction (intensity coupling efficiency : ℝ)
    (htotal : intensity * efficiency ≠ 0) :
    coincidenceRate intensity coupling efficiency / (intensity * efficiency) =
      coupling * efficiency := by
  have hfactor : coincidenceRate intensity coupling efficiency =
      (intensity * efficiency) * (coupling * efficiency) := by
    unfold coincidenceRate
    ring
  rw [hfactor, mul_div_cancel_left₀ _ htotal]

theorem conditional_fractions_at_balance (intensity coupling : ℝ)
    (hintensity : intensity ≠ 0) (hcoupling : coupling ≠ 0) :
    singleObserved intensity coupling (balancePoint coupling) /
        (intensity * balancePoint coupling) = 1 / 2 ∧
    coincidenceRate intensity coupling (balancePoint coupling) /
        (intensity * balancePoint coupling) = 1 / 2 := by
  have hbalance : balancePoint coupling ≠ 0 := by
    unfold balancePoint
    exact one_div_ne_zero (mul_ne_zero (by norm_num) hcoupling)
  have htotal := mul_ne_zero hintensity hbalance
  rw [conditional_single_fraction _ _ _ htotal, conditional_pair_fraction _ _ _ htotal]
  have hhalf : coupling * balancePoint coupling = 1 / 2 := by
    unfold balancePoint
    field_simp
  rw [hhalf]
  norm_num

theorem conditional_pair_probability (intensity coupling efficiency : ℝ)
    (htotal : intensity * efficiency ≠ 0)
    (hprobability : coupling * efficiency ∈ Set.Icc (0 : ℝ) 1) :
    coincidenceRate intensity coupling efficiency / (intensity * efficiency) ∈
      Set.Icc (0 : ℝ) 1 := by
  rwa [conditional_pair_fraction _ _ _ htotal]

theorem conditional_entropy_at_balance (intensity coupling : ℝ)
    (hintensity : intensity ≠ 0) (hcoupling : coupling ≠ 0) :
    Real.binEntropy (coincidenceRate intensity coupling (balancePoint coupling) /
      (intensity * balancePoint coupling)) / Real.log 2 = 1 := by
  rw [(conditional_fractions_at_balance intensity coupling hintensity hcoupling).2]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simpa using div_self hlog

theorem conditional_entropy_le_one (intensity coupling efficiency : ℝ) :
    Real.binEntropy (coincidenceRate intensity coupling efficiency /
      (intensity * efficiency)) / Real.log 2 ≤ 1 := by
  apply (div_le_iff₀ (Real.log_pos (by norm_num))).mpr
  simpa using (Real.binEntropy_le_log_two (p :=
    coincidenceRate intensity coupling efficiency / (intensity * efficiency)))

theorem conditional_entropy_eq_one_iff (intensity coupling efficiency : ℝ)
    (htotal : intensity * efficiency ≠ 0) (hcoupling : coupling ≠ 0) :
    Real.binEntropy (coincidenceRate intensity coupling efficiency /
      (intensity * efficiency)) / Real.log 2 = 1 ↔ efficiency = balancePoint coupling := by
  rw [conditional_pair_fraction _ _ _ htotal,
    div_eq_one_iff_eq (ne_of_gt (Real.log_pos (by norm_num))), Real.binEntropy_eq_log_two]
  unfold balancePoint
  constructor
  · intro hhalf
    apply (eq_div_iff (mul_ne_zero (by norm_num) hcoupling)).mpr
    norm_num at hhalf
    nlinarith
  · rintro rfl
    field_simp

theorem amplitude_equipartition (energy gap : ℝ)
    (hbalance : amplitudeNormSq ⟨energy, energy⟩ = gap ^ 2) :
    energy ^ 2 = gap ^ 2 / 2 := by
  unfold amplitudeNormSq at hbalance
  nlinarith

theorem nonnegative_equipartition_energy (energy gap : ℝ)
    (henergy : 0 ≤ energy) (hgap : 0 ≤ gap)
    (hbalance : amplitudeNormSq ⟨energy, energy⟩ = gap ^ 2) :
    energy = gap / Real.sqrt 2 := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsquare := amplitude_equipartition energy gap hbalance
  apply (eq_div_iff (ne_of_gt hpositive)).mpr
  have hproduct : 0 ≤ energy * Real.sqrt 2 := mul_nonneg henergy hpositive.le
  have hequal : (energy * Real.sqrt 2) ^ 2 = gap ^ 2 := by
    rw [mul_pow, hsqrt]
    nlinarith
  nlinarith

theorem reflected_equipartition (energy gap : ℝ)
    (hbalance : amplitudeNormSq ⟨energy, energy⟩ = gap ^ 2) :
    amplitudeNormSq (andreevReflection ⟨energy, energy⟩) = gap ^ 2 := by
  rw [andreevReflection_normSq, hbalance]

theorem three_phase_amplitude_sum (amplitude : ℂ) :
    (∑ exponent ∈ Finset.range 3, amplitude * phase 3 ^ exponent) = 0 := by
  rw [← Finset.mul_sum, phase_sum 3 (by norm_num), mul_zero]

theorem three_phase_product (amplitude : ℂ) :
    amplitude * (amplitude * phase 3) * (amplitude * phase 3 ^ 2) = amplitude ^ 3 := by
  calc
    _ = amplitude ^ 3 * phase 3 ^ 3 := by ring
    _ = amplitude ^ 3 := by rw [phase_pow_order 3 (by norm_num), mul_one]

end InfoGeometry.Nuclear.AndreevCascadeInterferometer
