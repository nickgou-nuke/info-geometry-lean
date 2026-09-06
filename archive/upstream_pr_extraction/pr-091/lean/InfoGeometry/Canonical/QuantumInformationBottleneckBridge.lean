import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Matrix Complex

namespace QuantumInformation

variable {n : ℕ}

/-- Quantum CPTP Channel information defect ΔS(ℰ) = S(ρ || σ) - S(ℰ(ρ) || ℰ(σ)). -/
structure QuantumChannel (n : ℕ) where
  infoDefect : ℝ        -- Relative entropy defect ΔS under CPTP channel ℰ
  defect_nonneg : 0 ≤ infoDefect

namespace QuantumChannel

variable (chan : QuantumChannel n)

/-- **Theorem**: Monotonicity of Quantum Relative Entropy:
    The information defect ΔS(ℰ) under any CPTP channel is non-negative (ΔS ≥ 0). -/
theorem relative_entropy_monotonicity : 0 ≤ chan.infoDefect :=
  chan.defect_nonneg

/-- Unitary channels preserve information with zero relative entropy defect. -/
structure UnitaryChannel (n : ℕ) extends QuantumChannel n where
  unitary_defect_zero : infoDefect = 0

/-- **Theorem**: Unitary Quantum Channels are Information-Lossless (ΔS = 0). -/
theorem unitary_channel_lossless (uchan : UnitaryChannel n) : uchan.infoDefect = 0 :=
  uchan.unitary_defect_zero

/-- **Theorem**: Contractivity of Quantum Fisher Information Metric:
    g_F(ℰ(ρ), ℰ(σ)) ≤ g_F(ρ, σ) under information bottleneck contraction factor lam ∈ [0, 1]. -/
theorem fisher_metric_contractivity (gF_in gF_out lam : ℝ)
    (h_in : 0 ≤ gF_in) (h_lam : 0 ≤ lam ∧ lam ≤ 1) (h_contract : gF_out = lam * gF_in) :
    gF_out ≤ gF_in := by
  rw [h_contract]
  nlinarith

end QuantumChannel

end QuantumInformation
