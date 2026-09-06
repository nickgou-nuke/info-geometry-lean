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

namespace WessZuminoGauge

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Non-Abelian Lie Algebra Gauge Variation δ_θ(X) = θ * X - X * θ on matrix space. -/
def gaugeVariation (theta X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  theta * X - X * theta

/-- Lie Bracket Commutator [θ₁, θ₂] = θ₁ * θ₂ - θ₂ * θ₁. -/
def lieBracket (theta1 theta2 : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  theta1 * theta2 - theta2 * theta1

/-- **Theorem**: Gauge Variation Linearity: δ_θ(X + Y) = δ_θ(X) + δ_θ(Y). -/
theorem gauge_variation_add (theta X Y : Matrix (Fin n) (Fin n) ℂ) :
    gaugeVariation theta (X + Y) = gaugeVariation theta X + gaugeVariation theta Y := by
  dsimp [gaugeVariation]
  noncomm_ring

/-- **Theorem**: Wess-Zumino Gauge Variation Commutator Identity:
    δ_θ₁(δ_θ₂ X) - δ_θ₂(δ_θ₁ X) = δ_[θ₁, θ₂](X). -/
theorem wess_zumino_gauge_variation_comm (theta1 theta2 X : Matrix (Fin n) (Fin n) ℂ) :
    gaugeVariation theta1 (gaugeVariation theta2 X) - gaugeVariation theta2 (gaugeVariation theta1 X) =
    gaugeVariation (lieBracket theta1 theta2) X := by
  dsimp [gaugeVariation, lieBracket]
  noncomm_ring

/-- Wess-Zumino Consistent Anomaly Functional A(θ, X) = Tr(θ * X - X * θ). -/
def anomalyFunctional (theta X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  trace (gaugeVariation theta X)

/-- **Theorem**: Vanishing Consistent Anomaly Trace under Trace Cyclic Property. -/
theorem consistent_anomaly_trace_zero (theta X : Matrix (Fin n) (Fin n) ℂ) :
    anomalyFunctional theta X = 0 := by
  dsimp [anomalyFunctional, gaugeVariation]
  rw [trace_sub]
  have h_comm : trace (X * theta) = trace (theta * X) := trace_mul_comm X theta
  rw [h_comm, sub_self]

end WessZuminoGauge
