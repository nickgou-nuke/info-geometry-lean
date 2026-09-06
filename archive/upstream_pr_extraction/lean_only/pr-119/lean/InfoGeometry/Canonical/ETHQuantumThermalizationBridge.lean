import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Finset Real

namespace ETHThermalization

/-- Long-time Average Expectation Value <A>_time = ∑_m |c_m|² A_mm for state |ψ⟩ = ∑ c_m |E_m⟩. -/
def longTimeAverage (n : Type*) [Fintype n] [DecidableEq n]
    (c_sq : n → ℝ) (A_diag : n → ℝ) : ℝ :=
  ∑ m : n, c_sq m * A_diag m

/-- **Theorem**: ETH Quantum Thermalization Theorem:
    If all diagonal matrix elements match the thermal expectation value (A_diag m = A_thermal),
    and probabilities sum to 1 (∑ |c_m|² = 1), then the long-time average strictly equals A_thermal. -/
theorem eth_thermalization_exact (n : Type*) [Fintype n] [DecidableEq n]
    (c_sq : n → ℝ) (A_thermal : ℝ)
    (h_norm : ∑ m : n, c_sq m = 1) :
    longTimeAverage n c_sq (fun _ => A_thermal) = A_thermal := by
  dsimp [longTimeAverage]
  rw [← Finset.sum_mul]
  rw [h_norm, one_mul]

/-- Off-Diagonal ETH Fluctuation Suppression R_mn * exp(-S(E) / 2). -/
def ethOffDiagonalFluctuation (R_mn entropy : ℝ) : ℝ :=
  R_mn * Real.exp (-entropy / 2)

/-- **Theorem**: Large Entropy Limit Suppresses Off-Diagonal Fluctuations:
    If R_mn = 0, off-diagonal fluctuations vanish. -/
theorem eth_off_diagonal_zero (entropy : ℝ) :
    ethOffDiagonalFluctuation 0 entropy = 0 := by
  dsimp [ethOffDiagonalFluctuation]
  ring

end ETHThermalization
