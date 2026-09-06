import InfoGeometry.Physics.MatrixTraceBimodulePairingNative
import Mathlib.Data.Real.Sqrt

/-!
# Probability amplitudes and a trace-attention readout

This owner records three finite algebraic readouts: the square-root/Born
identity, the trace pairing of left/right matrix actions, and a deliberately
linear toy positional action.  The latter is not asserted to be an analytic
modular flow or a quantum-information metric.
-/

noncomputable section

namespace InfoGeometry.Physics

variable {n : Type*} [Fintype n] [DecidableEq n]

def probabilityToAmplitude (p : ℝ) : ℝ := Real.sqrt p

theorem born_rule_recovery (p : ℝ) (hp : 0 ≤ p) :
    probabilityToAmplitude p * probabilityToAmplitude p = p := by
  exact Real.mul_self_sqrt hp

def attentionEntanglementScore
    (Q_context K_memory : TraceOperatorSpace n) : ℝ :=
  tracePairingNative (leftActionNative Q_context 1) (rightActionNative K_memory 1)

theorem attention_is_trace_pairing (Q K : TraceOperatorSpace n) :
    attentionEntanglementScore Q K = Matrix.trace (Q * K) := by
  change Matrix.trace ((Q * (1 : TraceOperatorSpace n)) *
      ((1 : TraceOperatorSpace n) * K)) = Matrix.trace (Q * K)
  simp

def hyperRoPE (tau : ℝ) (X : TraceOperatorSpace n) : TraceOperatorSpace n := tau • X

def mappingCylinderAttention
    (tau : ℝ) (Q K : TraceOperatorSpace n) : ℝ :=
  attentionEntanglementScore (hyperRoPE tau Q) K

theorem hyperRoPE_zero (X : TraceOperatorSpace n) : hyperRoPE 0 X = 0 := by
  simp [hyperRoPE]

end InfoGeometry.Physics
