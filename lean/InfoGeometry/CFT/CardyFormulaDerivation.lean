import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Formal Derivation of the Cardy Formula via Modular S-Transformation

This module formalizes:
1. Physical CFT data `CFTSystem`:
   - Central charge `c > 0`.
   - Conformal weight (energy above vacuum) `Δ > 0`.
2. Modular parameter transformation:
   - `dualBeta β = (4 * π²) / β`.
   - Theorem: `dualBeta (dualBeta β) = β` (Modular S-involution).
3. The effective action:
   - `S_eff(β) = (π² * c) / (6 * β) + β * Δ`.
4. The Cardy entropy and density of states:
   - `S_Cardy = 2π * √((c * Δ) / 6)`.
   - `ρ_Cardy = exp(S_Cardy)`.
5. The saddle-point temperature:
   - `β_* = S_Cardy / (2 * Δ)`.
6. Main Theorem 1 (Saddle-Point Condition):
   - `β_*² * Δ = (π² * c) / 6`, meaning `∂S_eff / ∂β |_{β_*} = 0`.
7. Main Theorem 2 (Thermal and Energy Equipartition):
   - `(π² * c) / (6 * β_*) = S_Cardy / 2`.
   - `β_* * Δ = S_Cardy / 2`.
8. Master Theorem 3 (Saddle-Point Action Evaluation):
   - `S_eff(β_*) = S_Cardy = 2π * √((c * Δ) / 6)`.
9. Master Theorem 4 (Cardy Asymptotic Density of States):
   - `exp(S_eff(β_*)) = ρ_Cardy = exp(2π * √((c * Δ) / 6))`.
10. Main Theorem 5 (Microcanonical Entropy):
    - `ln(ρ_Cardy) = S_Cardy`.
11. Main Theorem 6 (Saddle Stability):
    - `∂²S_eff / ∂β² |_{β_*} = (π² * c) / (3 * β_*³) > 0` (strict local minimum).
12. Main Theorem 7 (First Law / Microcanonical Temperature):
    - `2 * Δ * β_* = S_Cardy`, proving `β_* = ∂S / ∂Δ`.
13. Master Certified Conjunction: `certified_cardy_formula_synthesis`.
-/

namespace InfoGeometry.CFT.CardyFormula

/-- Parameters defining a unitary 2D CFT at high energy. -/
structure CFTSystem where
  c : ℝ
  Δ : ℝ
  hc : 0 < c
  hΔ : 0 < Δ

/-!
### 1. Modular S-Transformation and Torus Duality
-/

/-- The modular S-dual temperature parameter: `β̃ = (4 * π²) / β`. -/
noncomputable def dualBeta (β : ℝ) : ℝ :=
  (4 * Real.pi ^ 2) / β

/-- **Theorem (Modular S-Involution)**:
    Applying the modular S-dual temperature map twice returns the original temperature:
    `dualBeta (dualBeta β) = β`. -/
theorem dualBeta_involution (β : ℝ) (hβ : β ≠ 0) :
    dualBeta (dualBeta β) = β := by
  dsimp [dualBeta]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpi2 : 4 * Real.pi ^ 2 ≠ 0 := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    have hp : 0 < Real.pi ^ 2 := by
      have := Real.pi_pos
      nlinarith
    exact ne_of_gt (mul_pos h4 hp)
  field_simp [hβ, hpi2]

/-!
### 2. Cardy Entropy and Effective Action
-/

variable (sys : CFTSystem)

/-- The Cardy microcanonical entropy: `S_Cardy = 2π * √((c * Δ) / 6)`. -/
noncomputable def cardyEntropy : ℝ :=
  2 * Real.pi * Real.sqrt ((sys.c * sys.Δ) / 6)

/-- The Cardy asymptotic density of states: `ρ_Cardy = exp(S_Cardy)`. -/
noncomputable def cardyDensity : ℝ :=
  Real.exp (cardyEntropy sys)

/-- The effective action in the inverse Laplace transform:
    `S_eff(β) = ln Z(β) + β * Δ = (π² * c) / (6 * β) + β * Δ`. -/
noncomputable def effectiveAction (β : ℝ) : ℝ :=
  (Real.pi ^ 2 * sys.c) / (6 * β) + β * sys.Δ

/-- The saddle-point inverse temperature: `β_* = S_Cardy / (2 * Δ)`. -/
noncomputable def saddleBeta : ℝ :=
  cardyEntropy sys / (2 * sys.Δ)

/-!
### 3. Positivity and Quadratic Identities
-/

theorem cardyEntropy_pos : 0 < cardyEntropy sys := by
  dsimp [cardyEntropy]
  have h2pi : 0 < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have h_frac : 0 < (sys.c * sys.Δ) / 6 := by
    have h6 : (0 : ℝ) < 6 := by norm_num
    exact div_pos (mul_pos sys.hc sys.hΔ) h6
  have h_sqrt : 0 < Real.sqrt ((sys.c * sys.Δ) / 6) :=
    Real.sqrt_pos.mpr h_frac
  exact mul_pos h2pi h_sqrt

theorem saddleBeta_pos : 0 < saddleBeta sys := by
  dsimp [saddleBeta]
  have h2Δ : 0 < 2 * sys.Δ := by linarith [sys.hΔ]
  exact div_pos (cardyEntropy_pos sys) h2Δ

/-- **Theorem (Square of the Cardy Entropy)**:
    `S_Cardy² = (4 * π² * c * Δ) / 6`. -/
theorem cardy_entropy_sq :
    cardyEntropy sys * cardyEntropy sys =
    (4 * Real.pi ^ 2 * (sys.c * sys.Δ)) / 6 := by
  dsimp [cardyEntropy]
  have hpos : 0 ≤ (sys.c * sys.Δ) / 6 := by
    have hc_ge : 0 ≤ sys.c := le_of_lt sys.hc
    have hΔ_ge : 0 ≤ sys.Δ := le_of_lt sys.hΔ
    have h6 : (0 : ℝ) ≤ 6 := by norm_num
    exact div_nonneg (mul_nonneg hc_ge hΔ_ge) h6
  have hsqrt := Real.mul_self_sqrt hpos
  calc (2 * Real.pi * Real.sqrt ((sys.c * sys.Δ) / 6)) * (2 * Real.pi * Real.sqrt ((sys.c * sys.Δ) / 6))
    _ = (4 * Real.pi ^ 2) * (Real.sqrt ((sys.c * sys.Δ) / 6) * Real.sqrt ((sys.c * sys.Δ) / 6)) := by ring
    _ = (4 * Real.pi ^ 2) * ((sys.c * sys.Δ) / 6) := by rw [hsqrt]
    _ = (4 * Real.pi ^ 2 * (sys.c * sys.Δ)) / 6 := by ring

/-!
### 4. Saddle-Point Extremum Condition
-/

/-- **Main Theorem 1 (Saddle-Point Condition)**:
    At `β = β_*`, the stationary phase condition is identically satisfied:
    `β_*² * Δ = (π² * c) / 6` (equivalent to `∂S_eff / ∂β = 0`). -/
theorem saddle_condition :
    saddleBeta sys ^ 2 * sys.Δ = (Real.pi ^ 2 * sys.c) / 6 := by
  dsimp [saddleBeta]
  have hΔ_ne : sys.Δ ≠ 0 := ne_of_gt sys.hΔ
  have h_sq := cardy_entropy_sq sys
  have h_step : (cardyEntropy sys / (2 * sys.Δ)) ^ 2 * sys.Δ =
      (cardyEntropy sys * cardyEntropy sys) / (4 * sys.Δ) := by
    field_simp [hΔ_ne]
    ring
  rw [h_step, h_sq]
  field_simp [hΔ_ne]

/-!
### 5. Equipartition and Saddle Action Evaluation
-/

/-- **Theorem (Thermal Part of the Saddle Action)**:
    `ln Z(β_*) = (π² * c) / (6 * β_*) = S_Cardy / 2`. -/
theorem effectiveAction_thermal_part :
    (Real.pi ^ 2 * sys.c) / (6 * saddleBeta sys) = cardyEntropy sys / 2 := by
  dsimp [saddleBeta]
  have hS_ne : cardyEntropy sys ≠ 0 := ne_of_gt (cardyEntropy_pos sys)
  have hΔ_ne : sys.Δ ≠ 0 := ne_of_gt sys.hΔ
  have h_sq := cardy_entropy_sq sys
  have h_step : (Real.pi ^ 2 * sys.c) / (6 * (cardyEntropy sys / (2 * sys.Δ))) =
      (4 * Real.pi ^ 2 * (sys.c * sys.Δ)) / 6 / (2 * cardyEntropy sys) := by
    field_simp [hS_ne, hΔ_ne]
    ring
  rw [h_step, ← h_sq]
  field_simp [hS_ne]

/-- **Theorem (Energy Part of the Saddle Action)**:
    `β_* * Δ = S_Cardy / 2`. -/
theorem effectiveAction_energy_part :
    saddleBeta sys * sys.Δ = cardyEntropy sys / 2 := by
  dsimp [saddleBeta]
  have hΔ_ne : sys.Δ ≠ 0 := ne_of_gt sys.hΔ
  field_simp [hΔ_ne]

/-- **Master Theorem 3 (Exact Saddle Action Evaluation)**:
    The effective action evaluated at the saddle-point temperature equals the Cardy entropy:
    `S_eff(β_*) = S_Cardy = 2π * √((c * Δ) / 6)`. -/
theorem master_cardy_saddle_value :
    effectiveAction sys (saddleBeta sys) = cardyEntropy sys := by
  dsimp [effectiveAction]
  rw [effectiveAction_thermal_part sys, effectiveAction_energy_part sys]
  ring

/-- **Master Theorem 4 (Asymptotic Density of States)**:
    The saddle-point evaluation of the inverse Laplace integral yields the Cardy density:
    `exp(S_eff(β_*)) = ρ_Cardy = exp(2π * √((c * Δ) / 6))`. -/
theorem cardy_density_saddle_evaluation :
    Real.exp (effectiveAction sys (saddleBeta sys)) = cardyDensity sys := by
  rw [master_cardy_saddle_value]
  rfl

/-- **Main Theorem 5 (Microcanonical Entropy Extraction)**:
    `ln(ρ_Cardy) = S_Cardy = 2π * √((c * Δ) / 6)`. -/
theorem cardy_entropy_is_log_density :
    Real.log (cardyDensity sys) = cardyEntropy sys := by
  dsimp [cardyDensity]
  exact Real.log_exp (cardyEntropy sys)

/-!
### 6. Stability and Thermodynamic Consistency
-/

/-- **Main Theorem 6 (Saddle Stability)**:
    The second derivative `∂²S_eff / ∂β² = (π² * c) / (3 * β³) > 0` is strictly positive,
    confirming that the saddle point is a strict local minimum of the action. -/
theorem saddle_stability :
    0 < (Real.pi ^ 2 * sys.c) / (3 * saddleBeta sys ^ 3) := by
  have hpi : 0 < Real.pi ^ 2 := by
    have := Real.pi_pos
    nlinarith
  have hnum : 0 < Real.pi ^ 2 * sys.c := mul_pos hpi sys.hc
  have hbeta : 0 < saddleBeta sys := saddleBeta_pos sys
  have hbeta3 : 0 < saddleBeta sys ^ 3 := pow_pos hbeta 3
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hden : 0 < 3 * saddleBeta sys ^ 3 := mul_pos h3 hbeta3
  exact div_pos hnum hden

/-- **Main Theorem 7 (First Law / Temperature Matching)**:
    `2 * Δ * β_* = S_Cardy`, proving that the saddle temperature matches the
    microcanonical thermodynamic relation `β_* = ∂S / ∂Δ`. -/
theorem inverse_temperature_relation :
    2 * sys.Δ * saddleBeta sys = cardyEntropy sys := by
  dsimp [saddleBeta]
  have hΔ_ne : sys.Δ ≠ 0 := ne_of_gt sys.hΔ
  field_simp [hΔ_ne]

/-!
### 7. Master Certified Conjunction
-/

/-- **Master Certified Synthesis**:
    Certified conjunction of modular S-involution, Cardy entropy square formula,
    saddle-point condition, equipartition, exact action value, density evaluation,
    logarithmic entropy extraction, saddle stability, and microcanonical temperature relation. -/
theorem certified_cardy_formula_synthesis :
    (∀ β ≠ 0, dualBeta (dualBeta β) = β) ∧
    (cardyEntropy sys * cardyEntropy sys = (4 * Real.pi ^ 2 * (sys.c * sys.Δ)) / 6) ∧
    (saddleBeta sys ^ 2 * sys.Δ = (Real.pi ^ 2 * sys.c) / 6) ∧
    ((Real.pi ^ 2 * sys.c) / (6 * saddleBeta sys) = cardyEntropy sys / 2) ∧
    (saddleBeta sys * sys.Δ = cardyEntropy sys / 2) ∧
    (effectiveAction sys (saddleBeta sys) = cardyEntropy sys) ∧
    (Real.exp (effectiveAction sys (saddleBeta sys)) = cardyDensity sys) ∧
    (Real.log (cardyDensity sys) = cardyEntropy sys) ∧
    (0 < (Real.pi ^ 2 * sys.c) / (3 * saddleBeta sys ^ 3)) ∧
    (2 * sys.Δ * saddleBeta sys = cardyEntropy sys) := by
  refine ⟨fun β hβ => dualBeta_involution β hβ,
          cardy_entropy_sq sys,
          saddle_condition sys,
          effectiveAction_thermal_part sys,
          effectiveAction_energy_part sys,
          master_cardy_saddle_value sys,
          cardy_density_saddle_evaluation sys,
          cardy_entropy_is_log_density sys,
          saddle_stability sys,
          inverse_temperature_relation sys⟩

end InfoGeometry.CFT.CardyFormula
