import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.CartanExponentialAmariPotentialBridge

noncomputable section

/-- A positive scalar partition readout on a one-dimensional Cartan chart. -/
structure PositivePartition where
  Z : ℝ → ℝ
  positive : ∀ s, 0 < Z s

def logPotential (P : PositivePartition) (s : ℝ) : ℝ := Real.log (P.Z s)

def cartanHomogeneous (s : ℝ) : ℝ × ℝ :=
  (Real.exp (s / 2), Real.exp (-s / 2))

theorem logPotential_exp (P : PositivePartition) (s : ℝ) :
    Real.exp (logPotential P s) = P.Z s := by
  unfold logPotential
  exact Real.exp_log (P.positive s)

theorem logPotential_eq_log_partition (P : PositivePartition) (s : ℝ) :
    logPotential P s = Real.log (P.Z s) := by
  rfl

theorem cartanHomogeneous_first_ne_zero (s : ℝ) :
    (cartanHomogeneous s).1 ≠ 0 := by
  simp [cartanHomogeneous]

theorem cartanHomogeneous_second_ne_zero (s : ℝ) :
    (cartanHomogeneous s).2 ≠ 0 := by
  simp [cartanHomogeneous]

theorem cartanHomogeneous_ratio (s : ℝ) :
    (cartanHomogeneous s).1 / (cartanHomogeneous s).2 = Real.exp s := by
  unfold cartanHomogeneous
  rw [← Real.exp_sub]
  congr 1
  ring

theorem cartanHomogeneous_ratio_log (s : ℝ) :
    Real.log ((cartanHomogeneous s).1 / (cartanHomogeneous s).2) = s := by
  rw [cartanHomogeneous_ratio]
  exact Real.log_exp s

theorem logPotential_explicit (P : PositivePartition) (s : ℝ) :
    Real.exp (logPotential P s) = P.Z s ∧
      logPotential P s = Real.log (P.Z s) := by
  exact ⟨logPotential_exp P s, logPotential_eq_log_partition P s⟩

end

end InfoGeometry.Canonical.CartanExponentialAmariPotentialBridge

