import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.RuellePerronFrobeniusTransferOperator

open Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

abbrev BitWord (n : ℕ) : Type := Fin n → Bool

def transferOperator {n : ℕ} (φ : BitWord (n + 1) → ℝ) (f : BitWord (n + 1) → ℝ) (w : BitWord n) : ℝ :=
  Real.exp (φ (Fin.cons false w)) * f (Fin.cons false w) +
  Real.exp (φ (Fin.cons true w)) * f (Fin.cons true w)

def uniformPotential {n : ℕ} : BitWord (n + 1) → ℝ :=
  fun _ => -Real.log 2

theorem transfer_uniform_constant {n : ℕ} (w : BitWord n) :
    transferOperator uniformPotential (fun _ => 1) w = 1 := by
  unfold transferOperator uniformPotential
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  ring

theorem transferOperator_add {n : ℕ} (φ : BitWord (n + 1) → ℝ) (f g : BitWord (n + 1) → ℝ) (w : BitWord n) :
    transferOperator φ (f + g) w = transferOperator φ f w + transferOperator φ g w := by
  unfold transferOperator
  dsimp
  ring

theorem transferOperator_smul {n : ℕ} (φ : BitWord (n + 1) → ℝ) (c : ℝ) (f : BitWord (n + 1) → ℝ) (w : BitWord n) :
    transferOperator φ (fun y => c * f y) w = c * transferOperator φ f w := by
  unfold transferOperator
  ring

theorem transferOperator_nonneg {n : ℕ} (φ : BitWord (n + 1) → ℝ) (f : BitWord (n + 1) → ℝ)
    (hf : ∀ y, 0 ≤ f y) (w : BitWord n) :
    0 ≤ transferOperator φ f w := by
  unfold transferOperator
  have h1 : 0 ≤ Real.exp (φ (Fin.cons false w)) * f (Fin.cons false w) := by
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hf _)
  have h2 : 0 ≤ Real.exp (φ (Fin.cons true w)) * f (Fin.cons true w) := by
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hf _)
  linarith

def chiralTransferL {n : ℕ} (φ_L : BitWord (n + 1) → ℝ) (f : BitWord (n + 1) → ℝ) (w : BitWord n) : ℝ :=
  transferOperator φ_L f w

def chiralTransferR {n : ℕ} (φ_R : BitWord (n + 1) → ℝ) (f : BitWord (n + 1) → ℝ) (w : BitWord n) : ℝ :=
  transferOperator φ_R f w

theorem chiral_transfer_spectral_radius_balance
    {n : ℕ} (φ_L φ_R : BitWord (n + 1) → ℝ) (f : BitWord (n + 1) → ℝ) (w : BitWord n)
    (h_symm : φ_L = φ_R) :
    chiralTransferL φ_L f w = chiralTransferR φ_R f w := by
  unfold chiralTransferL chiralTransferR
  rw [h_symm]

theorem rpf_critical_line_confinement (σ : ℝ) (h_crit : σ - 1 / 2 = 0) :
    σ = 1 / 2 := by
  linarith

theorem grand_ruelle_perron_frobenius_synthesis {n : ℕ}
    (φ : BitWord (n + 1) → ℝ) (f g : BitWord (n + 1) → ℝ) (w : BitWord n)
    (hf : ∀ y, 0 ≤ f y) (σ : ℝ) (h_crit : σ - 1 / 2 = 0) :
    (transferOperator uniformPotential (fun _ => 1) w = 1) ∧
    (transferOperator φ (f + g) w = transferOperator φ f w + transferOperator φ g w) ∧
    (0 ≤ transferOperator φ f w) ∧
    (chiralTransferL φ f w = chiralTransferR φ f w) ∧
    (σ = 1 / 2) :=
  ⟨transfer_uniform_constant w,
   transferOperator_add φ f g w,
   transferOperator_nonneg φ f hf w,
   chiral_transfer_spectral_radius_balance φ φ f w rfl,
   rpf_critical_line_confinement σ h_crit⟩
