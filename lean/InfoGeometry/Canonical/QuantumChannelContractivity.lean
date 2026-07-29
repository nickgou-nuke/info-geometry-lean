import Mathlib.Analysis.Complex.Basic
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

namespace QuantumChannelContractivity

variable {n m : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)] [Fintype (Fin m)] [DecidableEq (Fin m)]

/-- Kraus Representation Quantum Channel Operator Φ(ρ) = K * ρ * K† with K† * K = 1. -/
structure KrausQuantumChannel (n m : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] [Fintype (Fin m)] [DecidableEq (Fin m)] where
  K_val : Matrix (Fin m) (Fin n) ℂ
  h_kraus_isometry : K_val.conjTranspose * K_val = 1

namespace KrausQuantumChannel

variable (channel : KrausQuantumChannel n m)

/-- Quantum Channel Action Φ(ρ) = K * ρ * K†. -/
def apply (rho : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  channel.K_val * rho * channel.K_val.conjTranspose

/-- **Theorem**: Quantum Channel Trace Preservation: Tr(Φ(ρ)) = Tr(ρ). -/
theorem trace_preserving (rho : Matrix (Fin n) (Fin n) ℂ) :
    trace (channel.apply rho) = trace rho := by
  dsimp [apply]
  have h_comm : trace (channel.K_val * rho * channel.K_val.conjTranspose) = trace (channel.K_val.conjTranspose * (channel.K_val * rho)) := by
    rw [trace_mul_comm]
  rw [h_comm, ← Matrix.mul_assoc, channel.h_kraus_isometry, one_mul]

/-- **Theorem**: Quantum Channel Hermiticity Preservation: (Φ(ρ))† = Φ(ρ†). -/
theorem hermiticity_preserving (rho : Matrix (Fin n) (Fin n) ℂ) :
    (channel.apply rho).conjTranspose = channel.apply rho.conjTranspose := by
  dsimp [apply]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc]

end KrausQuantumChannel

end QuantumChannelContractivity
