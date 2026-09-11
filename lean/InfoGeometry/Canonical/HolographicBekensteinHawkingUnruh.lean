import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace HolographicBekensteinHawking

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Bekenstein-Hawking Entropy S_BH(A) = Tr(A) / (4 * lp²) for horizon area matrix A. -/
def bekensteinHawkingEntropy (A : Matrix (Fin n) (Fin n) ℂ) (lp : ℂ) : ℂ :=
  trace A / (4 * lp^2)

/-- **Theorem**: Bekenstein-Hawking Entropy Scale Linearity: S_BH(c • A) = c * S_BH(A). -/
theorem bekenstein_hawking_scaling (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (lp : ℂ) :
    bekensteinHawkingEntropy (c • A) lp = c * bekensteinHawkingEntropy A lp := by
  dsimp [bekensteinHawkingEntropy]
  rw [trace_smul, smul_eq_mul]
  ring

/-- Unruh Thermal Density Matrix ρ_Unruh(Z, H_boost) = (1 / Z) • H_boost. -/
structure UnruhThermalState (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  H_boost : Matrix (Fin n) (Fin n) ℂ
  Z_partition : ℂ
  h_partition_nonzero : Z_partition ≠ 0
  h_partition_eq_trace : trace H_boost = Z_partition

namespace UnruhThermalState

variable (state : UnruhThermalState n)

/-- Unruh Density Matrix Operator ρ = (1 / Z) • H_boost. -/
def densityMatrix : Matrix (Fin n) (Fin n) ℂ :=
  (1 / state.Z_partition) • state.H_boost

/-- **Theorem**: Unruh Density Matrix Trace Normalization: Tr(ρ_Unruh) = 1. -/
theorem density_matrix_normalized : trace state.densityMatrix = 1 := by
  dsimp [densityMatrix]
  rw [trace_smul, smul_eq_mul, state.h_partition_eq_trace]
  rw [one_div, inv_mul_cancel₀ state.h_partition_nonzero]

/-- **Theorem**: Unruh Expectation Value Functional <O> = Tr(ρ * O) Linearity. -/
theorem unruh_expectation_add (O1 O2 : Matrix (Fin n) (Fin n) ℂ) :
    trace (state.densityMatrix * (O1 + O2)) = trace (state.densityMatrix * O1) + trace (state.densityMatrix * O2) := by
  rw [mul_add, trace_add]

end UnruhThermalState

end HolographicBekensteinHawking
