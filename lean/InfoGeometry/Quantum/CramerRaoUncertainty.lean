import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Quantum.CramerRaoUncertainty

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def quantumVarianceBound (v : ℝ) : Prop :=
  0 < v

def cramerRaoBound (v F : ℝ) : Prop :=
  v ≥ 1 / F

theorem cramer_rao_variance_product (v F : ℝ) (hF : 0 < F) (hCR : cramerRaoBound v F) :
    v * F ≥ 1 := by
  unfold cramerRaoBound at hCR
  have h_le : 1 / F ≤ v := hCR
  have h_mul : 1 / F * F ≤ v * F := mul_le_mul_of_nonneg_right h_le (le_of_lt hF)
  rw [one_div_mul_cancel (ne_of_gt hF)] at h_mul
  exact h_mul
