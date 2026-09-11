import Mathlib.Analysis.Calculus.Deriv.Comp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Infinitesimal affine-Casimir invariance

This file records the theorem-safe differential consequence of invariance along
an explicitly supplied one-parameter flow.  It deliberately does not infer a
Lie group, smooth coadjoint action, or an `ad*` operator from algebraic group
data alone.  Such an identification belongs to a later concrete owner.
-/

namespace InfoGeometry.Lie

noncomputable section

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
variable {S' : M → M →L[ℝ] ℝ}

/-- A one-parameter affine-flow carrier with its explicitly named infinitesimal
velocity.  The differentiability hypothesis is part of the carrier rather than
being inferred from the word `flow`. -/
structure InfinitesimalCurveFamilyDatum (M : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M] where
  /-- Parametrized flow curves starting at each point Q. Note: group law not assumed here. -/
  flow : ℝ → M → M
  /-- The flow at time 0 is the identity. -/
  flow_zero : ∀ Q, flow 0 Q = Q
  /-- The infinitesimal generator evaluated at Q. -/
  infinitesimal : M → M
  /-- The curve has the specified derivative at t = 0. -/
  flow_deriv : ∀ Q, HasDerivAt (fun t => flow t Q) (infinitesimal Q) 0

/-- A scalar observable is invariant under the given curve family. -/
def IsFlowInvariant (F : InfinitesimalCurveFamilyDatum M) (S : M → ℝ) : Prop :=
  ∀ t Q, S (F.flow t Q) = S Q

/-- The time derivative of an invariant observable is zero at t = 0. -/
theorem flow_invariant_deriv_zero {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (F : InfinitesimalCurveFamilyDatum M) (S : M → ℝ)
    (h_inv : IsFlowInvariant F S)
    (Q : M) :
    HasDerivAt (fun t => S (F.flow t Q)) 0 0 := by
  have h_const : (fun t => S (F.flow t Q)) = fun _ => S Q := by
    ext t
    exact h_inv t Q
  rw [h_const]
  exact hasDerivAt_const (0 : ℝ) (S Q)

/-- 
The fundamental calculus annihilation lemma: $dS_Q(V(Q)) = 0$.
Follows from chain rule on the invariant scalar observable.
-/
theorem flow_invariant_annihilates_infinitesimal {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (F : InfinitesimalCurveFamilyDatum M) (S : M → ℝ)
    (dS_Q : M →L[ℝ] ℝ)
    (h_inv : IsFlowInvariant F S)
    (Q : M)
    (h_diff : HasFDerivAt S dS_Q Q) :
    dS_Q (F.infinitesimal Q) = 0 := by
  have hchain :
      HasDerivAt (fun t : ℝ => S (F.flow t Q))
        (dS_Q (F.infinitesimal Q)) 0 := by
    simpa [Function.comp_def] using
      (h_diff).comp_hasDerivAt_of_eq 0 (F.flow_deriv Q)
        (by simpa using (F.flow_zero Q).symm)
  have hzero := flow_invariant_deriv_zero F S h_inv Q
  exact hchain.unique hzero

end

end InfoGeometry.Lie
