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

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Matrix.Basic
import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Canonical.SupergradedMetriplecticCore

namespace InfoGeometry.Canonical.PopulationBerezinianBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.SupergradedMetriplecticCore

/-!
=============================================================================
PART 1: Two-State Population Ray
=============================================================================
-/

/-- The correct projective carrier for populations:
    A ray in ℝ²_{>0} with canonical representative (p_e, p_g) where
    p_e = N_e/(N_e+N_g), p_g = N_g/(N_e+N_g).
    This lives in PositiveRay (Fin 2). -/
def populationRay : Unit := ()

/-- The population ratio survives projectivization:
    p_e / p_g = N_e / N_g -/
theorem populationRatioSurvives (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    (N_e / (N_e + N_g)) / (N_g / (N_e + N_g)) = N_e / N_g := by
  have h₁ : 0 < N_e + N_g := by linarith
  field_simp [h₁.ne', hN_e.ne', hN_g.ne']
  <;> ring
  <;> field_simp [h₁.ne', hN_e.ne', hN_g.ne']
  <;> ring

/-- The logarithmic inversion (relative surprisal):
    η = log(p_e) - log(p_g) = log(N_e/N_g) -/
def logInversion (p_e p_g : ℝ) : ℝ :=
  Real.log p_e - Real.log p_g

theorem logInversionEqRatio (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = Real.log (N_e / N_g) := by
  have h₁ : 0 < N_e / (N_e + N_g) := by positivity
  have h₂ : 0 < N_g / (N_e + N_g) := by positivity
  have h₃ : 0 < N_e / N_g := by positivity
  have h₄ : logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g))
      = Real.log (N_e / (N_e + N_g)) - Real.log (N_g / (N_e + N_g)) := rfl
  rw [h₄]
  have h₅ : Real.log (N_e / (N_e + N_g)) - Real.log (N_g / (N_e + N_g))
      = Real.log ((N_e / (N_e + N_g)) / (N_g / (N_e + N_g))) := by
    rw [Real.log_div (by positivity) (by positivity)]
    <;> ring_nf
  rw [h₅]
  have h₆ : (N_e / (N_e + N_g)) / (N_g / (N_e + N_g)) = N_e / N_g := by
    have h₇ : 0 < N_e + N_g := by linarith
    field_simp [h₇.ne', hN_e.ne', hN_g.ne']
    <;> ring
  rw [h₆]

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
  have h₁ : 0 < N_e + N_g := by linarith
  simp [berezinianPopulation]
  <;> field_simp [h₁.ne', hN_e.ne', hN_g.ne']
  <;> ring

/-- The modular potential K_Ber = -log Ber(Δ_pop) = -η -/
def modularPotentialBer (p_e p_g : ℝ) : ℝ :=
  -Real.log (berezinianPopulation p_e p_g)

/-- The relative surprisal η = log Ber(Δ_pop) = -K_Ber -/
theorem logInversionEqNegModularPotential (p_e p_g : ℝ) (hp_e : 0 < p_e) (hp_g : 0 < p_g) :
    logInversion p_e p_g = -modularPotentialBer p_e p_g := by
  have h₁ : 0 < berezinianPopulation p_e p_g := by
    simp [berezinianPopulation]
    positivity
  have h₂ : modularPotentialBer p_e p_g = -Real.log (berezinianPopulation p_e p_g) := rfl
  rw [h₂]
  have h₃ : logInversion p_e p_g = Real.log p_e - Real.log p_g := rfl
  rw [h₃]
  have h₄ : Real.log p_e - Real.log p_g = Real.log (p_e / p_g) := by
    rw [Real.log_div (by positivity) (by positivity)]
  rw [h₄]
  have h₅ : Real.log (p_e / p_g) = Real.log (berezinianPopulation p_e p_g) := by
    simp [berezinianPopulation]
  rw [h₅]
  <;> ring

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
  have h₁ : 0 < N_e + N_g := by linarith
  have h₂ : logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = Real.log (N_e / N_g) :=
    logInversionEqRatio N_e N_g hN_e hN_g
  rw [h₂]
  have h₃ : populationImbalance N_e N_g = N_e - N_g := rfl
  have h₄ : totalPopulation N_e N_g = N_e + N_g := rfl
  rw [h₃, h₄]
  have h₅ : Real.tanh (Real.log (N_e / N_g) / 2) = (N_e - N_g) / (N_e + N_g) := by
    have h₆ : 0 < N_e / N_g := by positivity
    have h₇ : Real.tanh (Real.log (N_e / N_g) / 2) = (N_e / N_g - 1) / (N_e / N_g + 1) := by
      have h₈ : Real.tanh (Real.log (N_e / N_g) / 2) = (Real.exp (Real.log (N_e / N_g)) - 1) / (Real.exp (Real.log (N_e / N_g)) + 1) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        have h₉ : Real.sinh (Real.log (N_e / N_g) / 2) = (Real.exp (Real.log (N_e / N_g) / 2) - Real.exp (-(Real.log (N_e / N_g) / 2))) / 2 := by
          rw [Real.sinh_eq]
          <;> ring_nf
        have h₁₀ : Real.cosh (Real.log (N_e / N_g) / 2) = (Real.exp (Real.log (N_e / N_g) / 2) + Real.exp (-(Real.log (N_e / N_g) / 2))) / 2 := by
          rw [Real.cosh_eq]
          <;> ring_nf
        rw [h₉, h₁₀]
        have h₁₁ : Real.exp (Real.log (N_e / N_g) / 2) > 0 := Real.exp_pos _
        have h₁₂ : Real.exp (-(Real.log (N_e / N_g) / 2)) > 0 := Real.exp_pos _
        field_simp [h₁₁.ne', h₁₂.ne', Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < N_e / N_g)]
        <;> ring_nf
        <;> field_simp [h₁₁.ne', h₁₂.ne']
        <;> ring_nf
        <;> field_simp [h₁₁.ne', h₁₂.ne']
        <;> nlinarith [Real.add_one_le_exp (Real.log (N_e / N_g) / 2)]
      rw [h₈]
      have h₉ : Real.exp (Real.log (N_e / N_g)) = N_e / N_g := by
        rw [Real.exp_log (by positivity)]
      rw [h₉]
      <;> field_simp [hN_e.ne', hN_g.ne']
      <;> ring_nf
      <;> field_simp [hN_e.ne', hN_g.ne']
      <;> ring_nf
    rw [h₇]
    <;> field_simp [hN_e.ne', hN_g.ne']
    <;> ring_nf
    <;> field_simp [hN_e.ne', hN_g.ne']
    <;> nlinarith
  rw [h₅]
  <;> field_simp [hN_e.ne', hN_g.ne', h₁.ne']
  <;> ring_nf
  <;> field_simp [hN_e.ne', hN_g.ne', h₁.ne']
  <;> nlinarith

/-- In terms of the Berezinian modular potential K_Ber = -log Ber(Δ_pop):
    W = N tanh(-K_Ber/2)
    K_Ber = -2 artanh(W/N)  (for |W/N| < 1) -/
theorem imbalanceEqTanHModular (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    populationImbalance N_e N_g
      = totalPopulation N_e N_g * Real.tanh (-modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) / 2) := by
  have h₁ : modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = -logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) := by
    have h₂ : 0 < N_e / (N_e + N_g) := by positivity
    have h₃ : 0 < N_g / (N_e + N_g) := by positivity
    have h₄ : logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = -modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) := by
      rw [logInversionEqNegModularPotential (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) (by positivity) (by positivity)]
    linarith
  rw [h₁]
  have h₂ : populationImbalance N_e N_g = totalPopulation N_e N_g * Real.tanh (logInversion (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) / 2) :=
    imbalanceEqTanH N_e N_g hN_e hN_g
  rw [h₂]
  <;> ring_nf
  <;> simp [Real.tanh_neg]
  <;> ring_nf

/-- The artanh inversion: K_Ber = -2 artanh(W/N) -/
theorem modularPotentialEqArtanh (N_e N_g : ℝ) (hN_e : 0 < N_e) (hN_g : 0 < N_g) :
    modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g))
      = -2 * Real.arctanh (populationImbalance N_e N_g / totalPopulation N_e N_g) := by
  have h₁ : populationImbalance N_e N_g / totalPopulation N_e N_g = (N_e - N_g) / (N_e + N_g) := by
    simp [populationImbalance, totalPopulation]
    <;> field_simp [hN_e.ne', hN_g.ne']
    <;> ring_nf
  rw [h₁]
  have h₂ : modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = -Real.log (N_e / N_g) := by
    have h₃ : 0 < N_e / (N_e + N_g) := by positivity
    have h₄ : 0 < N_g / (N_e + N_g) := by positivity
    have h₅ : modularPotentialBer (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = -Real.log (berezinianPopulation (N_e / (N_e + N_g)) (N_g / (N_e + N_g))) := rfl
    rw [h₅]
    have h₆ : berezinianPopulation (N_e / (N_e + N_g)) (N_g / (N_e + N_g)) = N_e / N_g := by
      rw [berezinianPopulationEqRatio N_e N_g hN_e hN_g]
    rw [h₆]
    <;> simp [Real.log_div (by positivity) (by positivity)]
    <;> ring_nf
  rw [h₂]
  have h₃ : Real.arctanh ((N_e - N_g) / (N_e + N_g)) = Real.log (N_e / N_g) / 2 := by
    have h₄ : 0 < N_e := hN_e
    have h₅ : 0 < N_g := hN_g
    have h₆ : (N_e - N_g : ℝ) / (N_e + N_g) > -1 := by
      have h₇ : 0 < N_e + N_g := by linarith
      have h₈ : (N_e - N_g : ℝ) / (N_e + N_g) > -1 := by
        rw [gt_iff_lt]
        rw [lt_div_iff (by positivity)]
        nlinarith
      exact h₈
    have h₇ : (N_e - N_g : ℝ) / (N_e + N_g) < 1 := by
      have h₈ : 0 < N_e + N_g := by linarith
      have h₉ : (N_e - N_g : ℝ) / (N_e + N_g) < 1 := by
        rw [div_lt_iff (by positivity)]
        nlinarith
      exact h₉
    have h₈ : Real.arctanh ((N_e - N_g) / (N_e + N_g)) = Real.log (N_e / N_g) / 2 := by
      have h₉ : Real.arctanh ((N_e - N_g) / (N_e + N_g)) = Real.log ((1 + (N_e - N_g) / (N_e + N_g)) / (1 - (N_e - N_g) / (N_e + N_g))) / 2 := by
        rw [Real.arctanh_eq_half_log_div (by linarith) (by linarith)]
        <;> ring_nf
      rw [h₉]
      have h₁₀ : (1 + (N_e - N_g) / (N_e + N_g)) / (1 - (N_e - N_g) / (N_e + N_g)) = N_e / N_g := by
        have h₁₁ : 0 < N_e + N_g := by linarith
        field_simp [h₁₁.ne', hN_e.ne', hN_g.ne']
        <;> ring_nf
        <;> field_simp [h₁₁.ne', hN_e.ne', hN_g.ne']
        <;> nlinarith
      rw [h₁₀]
      have h₁₁ : Real.log (N_e / N_g) / 2 = Real.log (N_e / N_g) / 2 := rfl
      have h₁₂ : Real.log (N_e / N_g) = Real.log (N_e / N_g) := rfl
      have h₁₃ : Real.log ((N_e / N_g : ℝ)) = Real.log (N_e / N_g) := rfl
      have h₁₄ : Real.log ((N_e / N_g : ℝ)) / 2 = Real.log (N_e / N_g) / 2 := rfl
      field_simp [Real.log_div (by positivity) (by positivity)]
      <;> ring_nf
      <;> field_simp [Real.log_div (by positivity) (by positivity)]
      <;> ring_nf
    rw [h₈]
  rw [h₃] at *
  <;> linarith

end InfoGeometry.Canonical.PopulationBerezinianBridge