import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset

namespace BMSSymmetry

/-- Discrete grid representation of the celestial sphere S² with area element w_i. -/
structure CelestialSphere (n : Type*) [Fintype n] [DecidableEq n] where
  w : n → ℝ        -- Area weights for quadrature on S²
  w_pos : ∀ i, 0 < w i

namespace CelestialSphere

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (S : CelestialSphere n)

/-- Bondi-Metzner-Sachs (BMS) supertranslation charge generator P_BMS(f) = ∑_i w_i * f_i * T_vv_i -/
def bmsCharge (f : n → ℝ) (T_vv : n → ℝ) : ℝ :=
  ∑ i : n, S.w i * f i * T_vv i

/-- **Theorem**: Supertranslation charge is strictly linear in the angle function f:
    P_BMS(f₁ + f₂) = P_BMS(f₁) + P_BMS(f₂). -/
theorem bms_charge_add (f1 f2 T_vv : n → ℝ) :
    S.bmsCharge (fun i => f1 i + f2 i) T_vv = S.bmsCharge f1 T_vv + S.bmsCharge f2 T_vv := by
  dsimp [bmsCharge]
  have h (i : n) : S.w i * (f1 i + f2 i) * T_vv i = S.w i * f1 i * T_vv i + S.w i * f2 i * T_vv i := by ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib]

/-- **Theorem**: Zero supertranslation yields zero BMS charge: P_BMS(0) = 0. -/
theorem bms_charge_zero (T_vv : n → ℝ) :
    S.bmsCharge (fun _ => 0) T_vv = 0 := by
  dsimp [bmsCharge]
  have h (i : n) : S.w i * 0 * T_vv i = 0 := by ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const_zero]

/-- Black hole soft hair entropy shift ΔS_soft(f) = (1 / 4 G ħ) * ∫ f dΩ -/
def softHairEntropyShift (f : n → ℝ) (G_hbar : ℝ) (hG : 0 < G_hbar) : ℝ :=
  (1 / (4 * G_hbar)) * ∑ i : n, S.w i * f i

/-- **Theorem**: Soft hair entropy shift is additive:
    ΔS_soft(f₁ + f₂) = ΔS_soft(f₁) + ΔS_soft(f₂). -/
theorem soft_hair_entropy_add (f1 f2 : n → ℝ) (G_hbar : ℝ) (hG : 0 < G_hbar) :
    S.softHairEntropyShift (fun i => f1 i + f2 i) G_hbar hG =
    S.softHairEntropyShift f1 G_hbar hG + S.softHairEntropyShift f2 G_hbar hG := by
  dsimp [softHairEntropyShift]
  have h (i : n) : S.w i * (f1 i + f2 i) = S.w i * f1 i + S.w i * f2 i := by ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, mul_add]

/-- **Theorem**: Soft hair entropy shift for uniform translation f(θ, ϕ) = c is proportional to total sphere area. -/
theorem soft_hair_entropy_constant (c G_hbar : ℝ) (hG : 0 < G_hbar) :
    S.softHairEntropyShift (fun _ => c) G_hbar hG =
    (c / (4 * G_hbar)) * ∑ i : n, S.w i := by
  dsimp [softHairEntropyShift]
  have h (i : n) : S.w i * c = c * S.w i := mul_comm _ _
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum]
  ring

end CelestialSphere

end BMSSymmetry
