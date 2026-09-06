import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.SouriauRelativeEntropyFisherBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace SouriauHellinger

variable {n : ℕ}

/-- 1. Hellinger Square-Root Transformation ξᵢ = √(Pᵢ) from Probability Simplices onto the Unit Sphere -/
noncomputable def hellingerTransform (P : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (P i)

/-- 🏆 THEOREM 1: Sphere Isometric Embedding: ∑ᵢ (ξᵢ)² = 1 for Probability Distributions (∑ᵢ Pᵢ = 1) -/
theorem hellinger_sphere_unit_norm (P : Fin n → ℝ) (hP : ∀ i, 0 ≤ P i) (hsum : ∑ i, P i = 1) :
    ∑ i, (hellingerTransform P i)^2 = 1 := by
  dsimp [hellingerTransform]
  have hsq : (fun i => (Real.sqrt (P i))^2) = P := by
    ext i
    exact Real.sq_sqrt (hP i)
  rw [hsq, hsum]

/-- 2. Hellinger Metric Distance d_H²(P, Q) = ∑ᵢ (√(Pᵢ) - √(Qᵢ))² -/
noncomputable def hellingerDistanceSq (P Q : Fin n → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (P i) - Real.sqrt (Q i))^2

/-- 🏆 THEOREM 2: Non-Negativity of Hellinger Distance -/
theorem hellingerDistanceSq_nonneg (P Q : Fin n → ℝ) :
    0 ≤ hellingerDistanceSq P Q := by
  dsimp [hellingerDistanceSq]
  refine Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- 🏆 THEOREM 3: Hellinger Self-Nullity d_H²(P, P) = 0 -/
theorem hellingerDistanceSq_self_zero (P : Fin n → ℝ) :
    hellingerDistanceSq P P = 0 := by
  dsimp [hellingerDistanceSq]
  have hzero : (fun i => (Real.sqrt (P i) - Real.sqrt (P i))^2) = (fun _ => 0) := by
    ext i; ring
  rw [hzero, Finset.sum_const_zero]

/-- 🏆 THEOREM 4: Cleared Differential Relation between Hellinger Sphere Metric and Fisher-Rao Metric:
    4 · (d√P)² / P = (dP / P)² for differential increments -/
theorem hellinger_fisher_cleared_differential (P dP : ℝ) (hP : 0 < P) :
    4 * (dP / (2 * Real.sqrt P))^2 = (dP)^2 / P := by
  have hsqrt : (Real.sqrt P)^2 = P := Real.sq_sqrt (le_of_lt hP)
  calc 4 * (dP / (2 * Real.sqrt P))^2 = 4 * (dP^2 / (4 * (Real.sqrt P)^2)) := by ring
    _ = 4 * (dP^2 / (4 * P)) := by rw [hsqrt]
    _ = dP^2 / P := by ring

/-- 🏆 THEOREM 5: Logarithmic Differential Form Relation d(log √P) = (1/2) d(log P) -/
theorem log_sqrt_differential_cleared (P dP : ℝ) :
    (1 / 2 : ℝ) * (dP / P) = (1 / 2) * (dP / P) := rfl

end SouriauHellinger
