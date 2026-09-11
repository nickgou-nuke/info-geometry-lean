import Mathlib.Analysis.ODE.PicardLindelof
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite operator carrier for context backreaction

This owner is the finite-basis specialization of the context equation.  It is
kept separate from the continuous-operator carrier: its finite-dimensional
instances are supplied by Mathlib, so Picard--Lindelöf existence is available
without postulating completeness for an infinite operator space.
-/

namespace InfoGeometry.Dynamics

noncomputable section

open scoped NNReal

variable {ι : Type*} [Fintype ι]

abbrev FiniteContextState := ι → ℝ

abbrev FiniteContextOperator :=
  FiniteContextState (ι := ι) →L[ℝ] FiniteContextState (ι := ι)

def finiteContextRhs
    (response : FiniteContextState (ι := ι) → FiniteContextOperator (ι := ι))
    (decayRate : ℝ) (D X : FiniteContextOperator (ι := ι))
    (ψ : FiniteContextState (ι := ι)) : FiniteContextOperator (ι := ι) :=
  response ψ - decayRate • X + (D.comp X - X.comp D)

theorem finiteContextRhs_eq_zero_of_balanced_commute
    (response : FiniteContextState (ι := ι) → FiniteContextOperator (ι := ι))
    (decayRate : ℝ) (D X : FiniteContextOperator (ι := ι))
    (ψ : FiniteContextState (ι := ι))
    (hcomm : D.comp X = X.comp D)
    (hbalance : response ψ = decayRate • X) :
    finiteContextRhs response decayRate D X ψ = 0 := by
  rw [finiteContextRhs, hcomm, sub_self, add_zero, hbalance, sub_self]

theorem finiteContextRhs_of_commute
    (response : FiniteContextState (ι := ι) → FiniteContextOperator (ι := ι))
    (decayRate : ℝ) (D X : FiniteContextOperator (ι := ι))
    (ψ : FiniteContextState (ι := ι))
    (hcomm : D.comp X = X.comp D) :
    finiteContextRhs response decayRate D X ψ = response ψ - decayRate • X := by
  rw [finiteContextRhs, hcomm, sub_self, add_zero]

structure FiniteContextTrajectory
    (response : FiniteContextState (ι := ι) → FiniteContextOperator (ι := ι))
    (decayRate : ℝ) (D : FiniteContextOperator (ι := ι))
    (ψ : ℝ → FiniteContextState (ι := ι)) where
  state : ℝ → FiniteContextOperator (ι := ι)
  equation : ∀ t, HasDerivAt state
    (finiteContextRhs response decayRate D (state t) (ψ t)) t

theorem exists_finiteContext_state_on_Icc
    (response : FiniteContextState (ι := ι) → FiniteContextOperator (ι := ι))
    (decayRate : ℝ) (D : FiniteContextOperator (ι := ι))
    (ψ : ℝ → FiniteContextState (ι := ι))
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax)
    (X₀ : FiniteContextOperator (ι := ι))
    {a r L K : ℝ≥0}
    (hR : IsPicardLindelof
      (fun t X => finiteContextRhs response decayRate D X (ψ t))
      t₀ X₀ a r L K)
    (hX : X₀ ∈ Metric.closedBall X₀ r) :
    ∃ X : ℝ → FiniteContextOperator (ι := ι), X t₀ = X₀ ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt X
          (finiteContextRhs response decayRate D (X t) (ψ t))
          (Set.Icc tmin tmax) t := by
  exact IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hR hX

def constant_finiteContextTrajectory
    (response : FiniteContextState (ι := ι) → FiniteContextOperator (ι := ι))
    (decayRate : ℝ) (D : FiniteContextOperator (ι := ι))
    (ψ : ℝ → FiniteContextState (ι := ι))
    (X : FiniteContextOperator (ι := ι))
    (heq : ∀ t, finiteContextRhs response decayRate D X (ψ t) = 0) :
    FiniteContextTrajectory response decayRate D ψ := by
  refine ⟨fun _ => X, ?_⟩
  intro t
  simpa [heq t] using (hasDerivAt_const (x := t) (c := X))

def balanced_commuting_finiteContextTrajectory
    (response : FiniteContextState (ι := ι) → FiniteContextOperator (ι := ι))
    (decayRate : ℝ) (D X : FiniteContextOperator (ι := ι))
    (ψ : ℝ → FiniteContextState (ι := ι))
    (hcomm : D.comp X = X.comp D)
    (hbalance : ∀ t, response (ψ t) = decayRate • X) :
    FiniteContextTrajectory response decayRate D ψ :=
  constant_finiteContextTrajectory response decayRate D ψ X
    (fun t => finiteContextRhs_eq_zero_of_balanced_commute
      response decayRate D X (ψ t) hcomm (hbalance t))

end
end InfoGeometry.Dynamics
