/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearConfigurationMixing

/-!
# Decay rates, branching, and conditional E2 inference

The finite index enumerates all de-excitation channels included in the model.
Completeness and physical rate laws are model inputs. A gamma channel's branch
is its partial rate divided by the TOTAL rate, not a gamma-only intensity ratio.
No RDDS/DSAM fit or nuclear lifetime is inferred from the supplied paper alone.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearDecayInference

open scoped BigOperators
open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
open InfoGeometry.Physics.SolovievTransitionStrength
open InfoGeometry.Physics.NuclearConfigurationMixing

variable {ι : Type*} [Fintype ι]

def totalRate (rates : ι → ℝ) : ℝ := ∑ j, rates j

/-- Mean lifetime in the constant-rate exponential decay model. -/
def meanLifetime (rates : ι → ℝ) : ℝ := 1 / totalRate rates

def halfLife (rates : ι → ℝ) : ℝ := Real.log 2 / totalRate rates

def branchFraction (rates : ι → ℝ) (j : ι) : ℝ := rates j / totalRate rates

theorem meanLifetime_pos (rates : ι → ℝ) (h : 0 < totalRate rates) :
    0 < meanLifetime rates := one_div_pos.mpr h

theorem branchFraction_sum (rates : ι → ℝ) (h : totalRate rates ≠ 0) :
    (∑ j, branchFraction rates j) = 1 := by
  simp only [branchFraction, ← Finset.sum_div]
  exact div_self h

theorem branchFraction_bounds (rates : ι → ℝ) (j : ι)
    (hn : ∀ k, 0 ≤ rates k) (ht : 0 < totalRate rates) :
    0 ≤ branchFraction rates j ∧ branchFraction rates j ≤ 1 := by
  refine ⟨div_nonneg (hn j) ht.le, (div_le_one ht).mpr ?_⟩
  exact Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ j)

theorem partialRate_from_branch (rates : ι → ℝ) (j : ι)
    (h : totalRate rates ≠ 0) :
    branchFraction rates j / meanLifetime rates = rates j := by
  unfold branchFraction meanLifetime
  field_simp

theorem meanLifetime_eq_halfLife_div_log_two (rates : ι → ℝ) :
    meanLifetime rates = halfLife rates / Real.log 2 := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold meanLifetime halfLife
  by_cases h : totalRate rates = 0
  · simp [h]
  · field_simp

/-- The name `halfLife` agrees with the exponential survival law. -/
theorem survival_at_halfLife (rates : ι → ℝ) (h : 0 < totalRate rates) :
    Real.exp (-(totalRate rates) * halfLife rates) = (1 / 2 : ℝ) := by
  have he : -(totalRate rates) * halfLife rates = -Real.log 2 := by
    unfold halfLife
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Conditional pure-E2 inference. `κ` includes the chosen units and physical
constants. The rate-law equation is a hypothesis, not derived from finite algebra. -/
theorem e2_from_gamma_branch (rates : ι → ℝ) (j : ι) (κ energy B : ℝ)
    (ht : 0 < totalRate rates) (hκ : 0 < κ) (hE : 0 < energy)
    (hRate : rates j = κ * energy ^ 5 * B) :
    B = branchFraction rates j / (meanLifetime rates * κ * energy ^ 5) := by
  unfold branchFraction meanLifetime
  rw [hRate]
  field_simp

/-- When the observed branch counts photons AND conversion electrons, recover
the radiative reduced strength using its explicit conversion coefficient. -/
theorem e2_from_conversion_inclusive_branch (rates : ι → ℝ) (j : ι)
    (κ energy alpha B : ℝ)
    (ht : 0 < totalRate rates) (hκ : 0 < κ) (hE : 0 < energy) (hα : 0 ≤ alpha)
    (hRate : rates j = (1 + alpha) * (κ * energy ^ 5 * B)) :
    B = branchFraction rates j /
      (meanLifetime rates * (1 + alpha) * κ * energy ^ 5) := by
  have ha : 0 < 1 + alpha := by linarith
  unfold branchFraction meanLifetime
  rw [hRate]
  field_simp

/-- Compose the explicit operator readout with the radiative-rate hypothesis.
`twoJInitial` is twice the initial spin; `O` must contain reduced matrix elements. -/
theorem operator_strength_from_gamma_branch (rates : ι → ℝ) (j : ι)
    (κ energy : ℝ) (twoJInitial : ℕ) (O : Observable) (initial final : Carrier)
    (ht : 0 < totalRate rates) (hκ : 0 < κ) (hE : 0 < energy)
    (hRate : rates j = κ * energy ^ 5 * reducedStrength twoJInitial O initial final) :
    strength O initial final =
      ((twoJInitial : ℝ) + 1) * branchFraction rates j /
        (meanLifetime rates * κ * energy ^ 5) := by
  have hB := e2_from_gamma_branch rates j κ energy
    (reducedStrength twoJInitial O initial final) ht hκ hE hRate
  have hd : (twoJInitial : ℝ) + 1 ≠ 0 := by positivity
  unfold reducedStrength at hB
  calc
    strength O initial final =
        (strength O initial final / ((twoJInitial : ℝ) + 1)) *
          ((twoJInitial : ℝ) + 1) := by field_simp
    _ = _ := by rw [hB]; ring

/-- End-to-end two-final-state inference from ENERGY-CORRECTED radiative
partial rates. The states share an initial spin; both photon energies must be
positive. Zero normal amplitude remains an explicit, additional model input. -/
theorem intruder_weight_from_e2_rates (O : Observable) (initial : Carrier)
    (c s κ energy₁ energy₂ rate₁ rate₂ : ℝ) (twoJInitial : ℕ)
    (h : c ^ 2 + s ^ 2 = 1) (hκ : 0 < κ)
    (hE₁ : 0 < energy₁) (hE₂ : 0 < energy₂)
    (hN : amplitude O initial ![1, 0] = 0)
    (hI : amplitude O initial ![0, 1] ≠ 0)
    (hRate₁ : rate₁ = κ * energy₁ ^ 5 * reducedStrength twoJInitial O initial ![c, s])
    (hRate₂ : rate₂ = κ * energy₂ ^ 5 * reducedStrength twoJInitial O initial ![-s, c]) :
    (rate₁ / energy₁ ^ 5) / (rate₁ / energy₁ ^ 5 + rate₂ / energy₂ ^ 5) = s ^ 2 := by
  have hd : (twoJInitial : ℝ) + 1 ≠ 0 := by positivity
  have hk : κ / ((twoJInitial : ℝ) + 1) ≠ 0 := div_ne_zero (ne_of_gt hκ) hd
  have h₁ : rate₁ / energy₁ ^ 5 =
      (κ / ((twoJInitial : ℝ) + 1)) * strength O initial ![c, s] := by
    rw [hRate₁]
    unfold reducedStrength
    field_simp
  have h₂ : rate₂ / energy₂ ^ 5 =
      (κ / ((twoJInitial : ℝ) + 1)) * strength O initial ![-s, c] := by
    rw [hRate₂]
    unfold reducedStrength
    field_simp
  rw [h₁, h₂, ← mul_add, mul_div_mul_left _ _ hk]
  exact intruder_weight_from_strengths O initial c s h hN hI

end InfoGeometry.Physics.NuclearDecayInference
