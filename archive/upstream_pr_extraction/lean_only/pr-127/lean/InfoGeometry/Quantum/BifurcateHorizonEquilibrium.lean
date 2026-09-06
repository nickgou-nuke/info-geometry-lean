import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.BifurcateHorizonEquilibrium

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def spectralParameter (ξ : ℝ) : ℝ := (1 / 2 : ℝ) + ξ

theorem critical_line_of_chiral_balance (disp_L disp_R : ℝ) 
    (h_balanced : disp_L = disp_R) :
    let ξ := disp_R - disp_L
    let σ := spectralParameter ξ
    σ = 1 / 2 := by
  intro ξ σ
  have h_xi : ξ = 0 := by
    unfold ξ
    rw [h_balanced, sub_self]
  unfold σ spectralParameter
  rw [h_xi, add_zero]

theorem bifurcate_mirror_sum (ξ : ℝ) :
    spectralParameter ξ + spectralParameter (-ξ) = 1 := by
  unfold spectralParameter
  ring

theorem grand_bifurcate_horizon_synthesis (disp_L disp_R : ℝ)
    (h_balanced : disp_L = disp_R) (ξ : ℝ) :
    (spectralParameter (disp_R - disp_L) = 1 / 2) ∧
    (spectralParameter ξ + spectralParameter (-ξ) = 1) := by
  have h := critical_line_of_chiral_balance disp_L disp_R h_balanced
  exact ⟨h, bifurcate_mirror_sum ξ⟩
