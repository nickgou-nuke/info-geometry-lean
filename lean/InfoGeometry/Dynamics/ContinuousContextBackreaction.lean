import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Dynamics.EntropicTokenDynamics

/-!
# Continuous context backreaction

The algebraic context owner uses `Module.End`.  This owner is the analytic
interface for differentiable dynamics: context states are continuous linear
maps, so they carry the normed-space topology required by `HasDerivAt`.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

abbrev ContextOperator :=
  TokenHilbertSpace V →L[ℂ] TokenHilbertSpace V

structure ContinuousContextField where
  K : ContextOperator (V := V)
  decayRate : ℝ
  decayRate_pos : 0 < decayRate

def continuousContextDerivative (ctx : ContinuousContextField (V := V))
    (response : TokenHilbertSpace V → ContextOperator (V := V))
    (D : ContextOperator (V := V)) (ψ : TokenHilbertSpace V) :
    ContextOperator (V := V) :=
  response ψ - (ctx.decayRate : ℂ) • ctx.K +
    (D.comp ctx.K - ctx.K.comp D)

/-- A differentiable context trajectory contract on the continuous operator
    carrier.  This records an equation, not an existence assertion. -/
structure ContinuousContextTrajectory
    (ctx : ContinuousContextField (V := V))
    (response : TokenHilbertSpace V → ContextOperator (V := V))
    (D : ContextOperator (V := V))
    (ψ : ℝ → TokenHilbertSpace V) where
  state : ℝ → ContextOperator (V := V)
  equation : ∀ t, HasDerivAt (𝕜 := ℝ) state
    (continuousContextDerivative ctx response D (ψ t)) t

@[simp] theorem continuousContextDerivative_zero_response
    (ctx : ContinuousContextField (V := V))
    (response : TokenHilbertSpace V → ContextOperator (V := V))
    (D : ContextOperator (V := V)) (ψ : TokenHilbertSpace V)
    (h : response ψ = 0) :
    continuousContextDerivative ctx response D ψ =
      -(ctx.decayRate : ℂ) • ctx.K + (D.comp ctx.K - ctx.K.comp D) := by
  rw [continuousContextDerivative, h]
  congr 1
  rw [zero_sub]
  exact (neg_smul (ctx.decayRate : ℂ) ctx.K).symm

theorem continuousContextDerivative_decay_only
    (ctx : ContinuousContextField (V := V))
    (response : TokenHilbertSpace V → ContextOperator (V := V))
    (D : ContextOperator (V := V)) (ψ : TokenHilbertSpace V)
    (hresponse : response ψ = 0)
    (hcomm : D.comp ctx.K = ctx.K.comp D) :
    continuousContextDerivative ctx response D ψ =
      -(ctx.decayRate : ℂ) • ctx.K := by
  rw [continuousContextDerivative_zero_response ctx response D ψ hresponse, hcomm]
  simp

end
end InfoGeometry.Dynamics
