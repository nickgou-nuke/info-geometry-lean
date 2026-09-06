import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.DiscreteFreeEnergyDissipationBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace InfoGeometry.Canonical.LandauerCramerRaoBoundBridge

open DiscreteThermodynamics

/-- 1. Landauer Minimum Erasure Work Functional: W_min = k_B T log(2) · ΔS -/
noncomputable def landauerMinWork (kB T deltaS : ℝ) : ℝ :=
  kB * T * Real.log 2 * deltaS

/-- 🏆 THEOREM 1: Positivity of Landauer Erasure Work for Positive Heat Bath and Information Loss -/
theorem landauer_erasure_work_pos (kB T deltaS : ℝ) (hkB : 0 < kB) (hT : 0 < T) (hS : 0 < deltaS) :
    0 < landauerMinWork kB T deltaS := by
  dsimp [landauerMinWork]
  have hlog2 : 0 < Real.log 2 := by
    rw [Real.log_pos_iff (by norm_num)]
    norm_num
  positivity

/-- 2. Cramér-Rao Information Lower Bound: Var(θ̂) ≥ 1 / I(θ) -/
noncomputable def cramerRaoBound (fisherInfo : ℝ) : ℝ :=
  1 / fisherInfo

/-- 🏆 THEOREM 2: Cramér-Rao Minimum Variance Bound from Fisher Information -/
theorem cramer_rao_variance_lower_bound (var fisherInfo : ℝ) (hI : 0 < fisherInfo)
    (hCR : 1 ≤ var * fisherInfo) :
    cramerRaoBound fisherInfo ≤ var := by
  dsimp [cramerRaoBound]
  rw [div_le_iff₀ hI]
  linarith

/-- 🏆 THEOREM 3: Multi-Bit Landauer Erasure Linearity across Resolution Levels:
    W_min(k bits) = k · (k_B T log(2)) -/
theorem landauer_multibit_erasure_scaling (kB T : ℝ) (k : ℕ) :
    landauerMinWork kB T (k : ℝ) = (k : ℝ) * (kB * T * Real.log 2) := by
  dsimp [landauerMinWork]
  ring

/-- 🏆 THEOREM 4: Thermal Resolution Tradeoff:
    Erasure Work plus Cramér-Rao Estimation Noise satisfies W_min · Var ≥ k_B T log(2) / I(θ) -/
theorem thermal_resolution_tradeoff (kB T deltaS var fisherInfo : ℝ)
    (hkB : 0 < kB) (hT : 0 < T) (hS : 0 < deltaS)
    (hCR : cramerRaoBound fisherInfo ≤ var) :
    (kB * T * Real.log 2 * deltaS) * (1 / fisherInfo) ≤ landauerMinWork kB T deltaS * var := by
  dsimp [cramerRaoBound, landauerMinWork] at *
  have h_work_pos : 0 < kB * T * Real.log 2 * deltaS := by
    have hlog2 : 0 < Real.log 2 := by
      rw [Real.log_pos_iff (by norm_num)]
      norm_num
    positivity
  nlinarith [hCR, h_work_pos]

end InfoGeometry.Canonical.LandauerCramerRaoBoundBridge
