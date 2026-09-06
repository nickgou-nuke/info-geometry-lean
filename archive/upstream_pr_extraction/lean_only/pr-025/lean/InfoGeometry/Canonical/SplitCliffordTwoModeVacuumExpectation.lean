import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordTwoModeCAR

/-!
# InfoGeometry.Canonical.SplitCliffordTwoModeVacuumExpectation

Concrete two-mode vacuum expectation contractions in `M₄(ℝ)`.

This file uses the explicit operators `a1`, `a2`, `a1Dag`, `a2Dag` from
`SplitCliffordTwoModeCAR` and evaluates Wick base contractions by direct matrix
arithmetic.
-/

namespace InfoGeometry.Canonical.SplitCliffordTwoModeVacuumExpectation

open Matrix
open InfoGeometry.Canonical.SplitCliffordTwoModeCAR

abbrev V4R := Matrix (Fin 4) (Fin 1) ℝ

/-- Two-mode vacuum vector `|Ω⟩ = [1,0,0,0]ᵀ`. -/
def vac4 : V4R :=
  !![1;
     0;
     0;
     0]

/-- Vacuum expectation projection `⟨Ω|M|Ω⟩` as the `(0,0)` entry. -/
def vev4 (M : M4R) : ℝ := M 0 0

/-- Mode-1 forward contraction. -/
theorem vev4_a1_a1Dag :
    vev4 (a1 * a1Dag) = 1 := by
  change (a1 * a1Dag) 0 0 = 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, a1, a1Dag]

/-- Mode-1 reverse contraction. -/
theorem vev4_a1Dag_a1 :
    vev4 (a1Dag * a1) = 0 := by
  change (a1Dag * a1) 0 0 = 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, a1, a1Dag]

/-- Mode-2 forward contraction. -/
theorem vev4_a2_a2Dag :
    vev4 (a2 * a2Dag) = 1 := by
  change (a2 * a2Dag) 0 0 = 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, a2, a2Dag]

/-- Mode-2 reverse contraction. -/
theorem vev4_a2Dag_a2 :
    vev4 (a2Dag * a2) = 0 := by
  change (a2Dag * a2) 0 0 = 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, a2, a2Dag]

/-- Cross contraction vanishes: `⟨Ω|a₁ a₂†|Ω⟩ = 0`. -/
theorem vev4_cross_a1_a2Dag :
    vev4 (a1 * a2Dag) = 0 := by
  change (a1 * a2Dag) 0 0 = 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, a1, a2Dag]

/-- Cross contraction vanishes: `⟨Ω|a₂ a₁†|Ω⟩ = 0`. -/
theorem vev4_cross_a2_a1Dag :
    vev4 (a2 * a1Dag) = 0 := by
  change (a2 * a1Dag) 0 0 = 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, a2, a1Dag]

/-- Quartic Wick base identity in the two-mode vacuum. -/
theorem vev4_wick_base_quartic :
    vev4 (a1 * a2 * a2Dag * a1Dag) = 1 := by
  change (a1 * a2 * a2Dag * a1Dag) 0 0 = 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, a1, a2, a2Dag, a1Dag]

/-- `a₁` annihilates the two-mode vacuum. -/
theorem a1_vac4_zero :
    a1 * vac4 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a1, vac4, Matrix.mul_apply, Fin.sum_univ_four]

/-- `a₂` annihilates the two-mode vacuum. -/
theorem a2_vac4_zero :
    a2 * vac4 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a2, vac4, Matrix.mul_apply, Fin.sum_univ_four]

end InfoGeometry.Canonical.SplitCliffordTwoModeVacuumExpectation
