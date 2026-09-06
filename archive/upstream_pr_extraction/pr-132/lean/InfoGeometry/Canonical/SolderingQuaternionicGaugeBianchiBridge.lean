import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open Matrix Complex

namespace SolderingQuaternionicGauge

-- Real Pauli Basis for 2x2 Spacetime Soldering Frame
def sigma0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def sigma1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def sigma3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
def epsilon : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- Soldering Form Map σ: ℂ⁴ → M₂(ℂ) mapping 4-vectors (t, z, x, y) to 2x2 matrices. -/
def soldering (t z x y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  t • sigma0 + z • sigma3 + x • sigma1 + y • epsilon

/-- **Theorem**: Metric-Determinant Duality: det(soldering(t, z, x, y)) = t² - z² - x² + y². -/
theorem det_soldering_eq_metric (t z x y : ℂ) :
    (soldering t z x y).det = t^2 - z^2 - x^2 + y^2 := by
  simp [soldering, sigma0, sigma1, sigma3, epsilon, det_fin_two, Matrix.of_apply]
  ring

/-- **Theorem**: Trace of Soldering Form Matrix: Tr(soldering(t, z, x, y)) = 2t. -/
theorem trace_soldering (t z x y : ℂ) :
    trace (soldering t z x y) = 2 * t := by
  simp [soldering, sigma0, sigma1, sigma3, epsilon, trace, Fin.sum_univ_two, Matrix.of_apply]
  ring

/-- Parafermion Z_3 Phase ω = e^(2πi / 3). -/
def parafermionPhase : ℂ := Real.cos (2 * Real.pi / 3) + I * Real.sin (2 * Real.pi / 3)

/-- Z_3 Parafermion Generator Commutation Relation γ₁ γ₂ = ω γ₂ γ₁. -/
structure ParafermionPair where
  gamma1 : Matrix (Fin 3) (Fin 3) ℂ
  gamma2 : Matrix (Fin 3) (Fin 3) ℂ

namespace ParafermionPair

variable (para : ParafermionPair)

/-- **Theorem**: Parafermion Commutator Trace Vanishing: Tr(γ₁ γ₂ - ω γ₂ γ₁) = 0. -/
theorem parafermion_comm_trace_zero :
    (hcomm : para.gamma1 * para.gamma2 =
      parafermionPhase • (para.gamma2 * para.gamma1)) →
    trace (para.gamma1 * para.gamma2 - parafermionPhase • (para.gamma2 * para.gamma1)) = 0 := by
  intro hcomm
  rw [hcomm, sub_self, trace_zero]

/-- **Theorem**: Parafermion Trace Commutativity: Tr(γ₁ γ₂) = Tr(γ₂ γ₁). -/
theorem parafermion_trace_comm :
    trace (para.gamma1 * para.gamma2) = trace (para.gamma2 * para.gamma1) :=
  trace_mul_comm para.gamma1 para.gamma2

end ParafermionPair

end SolderingQuaternionicGauge
