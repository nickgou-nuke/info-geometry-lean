import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.SupergradedMetriplecticCore

/-!
# PopulationBerezinianBridge

Bridges the projective population ray to the Berezinian supervolume.

The audit identified:
- PositiveRay (Fin 1) carries NO population magnitude (normalized to 1)
- Correct carrier: q ∈ PositiveRay (Fin 2) with p_e = N_e/(N_e+N_g), p_g = N_g/(N_e+N_g)
- Population operator Δ_pop = diag(p_e, p_g) on the graded (1|1) space
- Ber(Δ_pop) = p_e/p_g = N_e/N_g
- η = log Ber(Δ_pop) (not -log Ber)
- W = N tanh(-K_Ber/2) where K_Ber = -log Ber(Δ_pop)

This file constructs the bridge and proves the exact relations.
-/

noncomputable section

namespace InfoGeometry.Canonical.PopulationBerezinianBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.SupergradedMetriplecticCore

/-!
=============================================================================
PART 1: Two-State Population Ray
=============================================================================
-/

/-- The population ratio survives projectivization:
    p_e / p_g = N_e / N_g -/
theorem populationRatioSurvives (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    (N_e / (N_e + N_g)) / (N_g / (N_e + N_g)) = N_e / N_g := by
  have h₁ : N_e + N_g ≠ 0 := by linarith
  have h₂ : N_g ≠ 0 := by linarith
  field_simp

/-- The logarithmic inversion (relative surprisal):
    η = log(p_e) - log(p_g) = log(N_e/N_g) -/
def logInversion (p_e p_g : ℝ) : ℝ :=
  Real.log p_e - Real.log p_g

theorem logInversionEqRatio (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = Real.log (N_e / N_g) := by
  have hsum : N_e + N_g ≠ 0 := by linarith
  have hNg : N_g ≠ 0 := by linarith
  unfold logInversion
  rw [Real.log_div hN_e.ne' hsum, Real.log_div hN_g.ne' hsum]
  ring_nf
  rw [← Real.log_div hN_e.ne' hNg, div_eq_mul_inv]

/-!
=============================================================================
PART 2: Population Berezinian
=============================================================================
-/

/-- The (1|1) graded population operator:
    Δ_pop = [[p_e, 0], [0, p_g]]
    where the even sector is excited state, odd sector is ground state. -/
def populationOperator (p_e p_g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p_e, 0; 0, p_g]

/-- Berezinian of the population operator:
    Ber(Δ_pop) = p_e / p_g (for even/odd grading) -/
def berezinianPopulation (p_e p_g : ℝ) : ℝ :=
  p_e / p_g

theorem berezinianPopulationEqRatio (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    berezinianPopulation (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = N_e / N_g := by
  have h₁ : N_e + N_g ≠ 0 := by linarith
  have h₂ : N_g ≠ 0 := by linarith
  simp [berezinianPopulation]
  field_simp

/-- The modular potential K_Ber = -log Ber(Δ_pop) = -η -/
def modularPotentialBer (p_e p_g : ℝ) : ℝ :=
  -Real.log (berezinianPopulation p_e p_g)

/-- The relative surprisal η = log Ber(Δ_pop) = -K_Ber -/
theorem logInversionEqNegModularPotential (p_e p_g : ℝ) (hp_e : 0 < p_e) (hp_g : 0 < p_g) :
    logInversion p_e p_g = -modularPotentialBer p_e p_g := by
  unfold logInversion modularPotentialBer berezinianPopulation
  rw [Real.log_div hp_e.ne' hp_g.ne']
  ring

/-!
=============================================================================
PART 3: Population Imbalance and TanH Relation
=============================================================================
-/

/-- Total population N = N_e + N_g -/
def totalPopulation (N_e N_g : ℝ) : ℝ := N_e + N_g

/-- Population imbalance W = N_e - N_g -/
def populationImbalance (N_e N_g : ℝ) : ℝ := N_e - N_g

/-- Key identity: W = N tanh(η/2) where η = log(N_e/N_g) -/
theorem imbalanceEqTanH (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    populationImbalance N_e N_g
      = totalPopulation N_e N_g * Real.tanh (logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) / 2) := by
  have hlog : logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = Real.log (N_e / N_g) :=
    logInversionEqRatio N_e N_g hN_e hN_g
  rw [hlog]
  unfold populationImbalance totalPopulation
  have h_ratio_pos : 0 < N_e / N_g := div_pos hN_e hN_g
  let u := Real.exp (Real.log (N_e / N_g) / 2)
  have hu_pos : 0 < u := Real.exp_pos _
  have hu_ne : u ≠ 0 := hu_pos.ne'
  have hu_sq : u ^ 2 = N_e / N_g := by
    dsimp [u]
    rw [sq, ← Real.exp_add]
    have h2 : Real.log (N_e / N_g) / 2 + Real.log (N_e / N_g) / 2 = Real.log (N_e / N_g) := by ring
    rw [h2, Real.exp_log h_ratio_pos]
  have h_tanh : Real.tanh (Real.log (N_e / N_g) / 2) = (N_e - N_g) / (N_e + N_g) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have h_u_neg : Real.exp (-(Real.log (N_e / N_g) / 2)) = u⁻¹ := by
      dsimp [u]
      rw [Real.exp_neg]
    rw [h_u_neg]
    have h_cancel_two : ((u - u⁻¹) / 2) / ((u + u⁻¹) / 2) = (u - u⁻¹) / (u + u⁻¹) := by
      rw [div_div_div_comm, div_self (by norm_num : (2:ℝ) ≠ 0), div_one]
    rw [h_cancel_two]
    have h_mult : (u - u⁻¹) / (u + u⁻¹) = (u ^ 2 - 1) / (u ^ 2 + 1) := by
      calc (u - u⁻¹) / (u + u⁻¹)
        _ = ((u - u⁻¹) * u) / ((u + u⁻¹) * u) := by rw [mul_div_mul_right _ _ hu_ne]
        _ = (u ^ 2 - 1) / (u ^ 2 + 1) := by
          congr 1
          · rw [sub_mul, inv_mul_cancel₀ hu_ne, sq]
          · rw [add_mul, inv_mul_cancel₀ hu_ne, sq]
    rw [h_mult, hu_sq]
    have hsum : N_e + N_g ≠ 0 := by linarith
    field_simp
  rw [h_tanh]
  have hsum : N_e + N_g ≠ 0 := by linarith
  field_simp

/-- In terms of the Berezinian modular potential K_Ber = -log Ber(Δ_pop):
    W = N tanh(-K_Ber/2) -/
theorem imbalanceEqTanHModular (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    populationImbalance N_e N_g
      = totalPopulation N_e N_g * Real.tanh (-modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) / 2) := by
  have h1 : -modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) =
      logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) :=
    (logInversionEqNegModularPotential _ _ (by positivity) (by positivity)).symm
  rw [h1]
  exact imbalanceEqTanH N_e N_g hN_e hN_g

/-- The artanh inversion: K_Ber = -2 artanh(W/N) -/
theorem modularPotentialEqArtanh (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g))
      = -2 * Real.artanh (populationImbalance N_e N_g / totalPopulation N_e N_g) := by
  have h_imb := imbalanceEqTanHModular N_e N_g hN_e hN_g
  have h_tot_pos : 0 < totalPopulation N_e N_g := by
    unfold totalPopulation
    linarith
  have h_div : populationImbalance N_e N_g / totalPopulation N_e N_g =
      Real.tanh (-modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) / 2) := by
    rw [h_imb]
    have hne : totalPopulation N_e N_g ≠ 0 := h_tot_pos.ne'
    field_simp
  rw [h_div, Real.artanh_tanh]
  ring

end InfoGeometry.Canonical.PopulationBerezinianBridge
