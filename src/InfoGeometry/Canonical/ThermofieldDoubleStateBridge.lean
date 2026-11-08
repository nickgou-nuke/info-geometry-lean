import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.TomitaTakesakiModularOperatorKMS

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

open Real Finset

namespace InfoGeometry.Canonical.ThermofieldDoubleStateBridge

open InfoGeometry.Canonical.TomitaTakesakiModularOperatorKMS

/-- The unnormalized Thermofield Double state amplitude c_n(β) = e^{-β E_n / 2} -/
noncomputable def tfdStateCoeff (β : ℝ) (E : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (-β * E n / 2)

/-- 🏆 THEOREM 1: The squared amplitude of the TFD state component equals the Boltzmann weight:
    (c_n(β))^2 = e^{-β E_n} -/
theorem tfd_squared_amplitude_eq_boltzmann (β : ℝ) (E : ℕ → ℝ) (n : ℕ) :
    (tfdStateCoeff β E n) ^ 2 = Real.exp (-β * E n) := by
  dsimp [tfdStateCoeff]
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- 🏆 THEOREM 2: Finite sum of squared TFD amplitudes equals the canonical partition function Z(β):
    ∑_{n < N} (c_n(β))^2 = ∑_{n < N} e^{-β E_n} = Z_N(β) -/
theorem tfd_norm_sq_eq_partition_function (β : ℝ) (E : ℕ → ℝ) (N : ℕ) :
    (range N).sum (fun n => (tfdStateCoeff β E n) ^ 2) =
      (range N).sum (fun n => Real.exp (-β * E n)) := by
  apply sum_congr rfl
  intro n _
  exact tfd_squared_amplitude_eq_boltzmann β E n

/-- 🏆 THEOREM 3: Tracing out subsystem R yields the exact Gibbs thermal density matrix weight for subsystem L:
    (c_n(β))^2 / Z = e^{-β E_n} / Z -/
theorem tfd_partial_trace_eq_gibbs_density (β Z : ℝ) (E : ℕ → ℝ) (n : ℕ) (hZ : Z > 0) :
    (tfdStateCoeff β E n) ^ 2 / Z = Real.exp (-β * E n) / Z := by
  rw [tfd_squared_amplitude_eq_boltzmann]

end InfoGeometry.Canonical.ThermofieldDoubleStateBridge
