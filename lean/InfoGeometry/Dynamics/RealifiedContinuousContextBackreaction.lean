import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Dynamics.RealifiedTokenOperatorBridge

/-!
# Realified continuous context backreaction

This owner keeps the coupled context equation on a genuine real normed
operator carrier.  Existence is obtained only from an explicit
`IsPicardLindelof` certificate for the response field.
-/

namespace InfoGeometry.Dynamics

noncomputable section

open scoped NNReal

variable {V : Type*} [Fintype V]

instance realTokenHilbertNormedSpace :
    NormedSpace ℝ (RealTokenHilbertSpace (V := V)) :=
  RestrictScalars.normedSpace ℝ ℂ (TokenHilbertSpace V)

instance (priority := 1100) realTokenHilbertModule :
    Module ℝ (RealTokenHilbertSpace (V := V)) :=
  (realTokenHilbertNormedSpace (V := V)).toModule

instance realTokenHilbertIsTopologicalAddGroup :
    IsTopologicalAddGroup (RealTokenHilbertSpace (V := V)) := by
  change IsTopologicalAddGroup (TokenHilbertSpace V)
  infer_instance

instance realTokenHilbertSMulCommClass :
    SMulCommClass ℝ ℝ (RealTokenHilbertSpace (V := V)) where
  smul_comm a b x := by
    simp only [smul_smul]
    rw [mul_comm]

abbrev RealContextOperator :=
  RealTokenHilbertSpace (V := V) →L[ℝ]
    RealTokenHilbertSpace (V := V)

instance realContextOperatorNormedAddCommGroup :
    NormedAddCommGroup (RealContextOperator (V := V)) := by
  change NormedAddCommGroup
    (RealTokenHilbertSpace (V := V) →SL[RingHom.id ℝ]
      RealTokenHilbertSpace (V := V))
  exact @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ
    (RealTokenHilbertSpace (V := V)) (RealTokenHilbertSpace (V := V))
    inferInstance inferInstance inferInstance inferInstance
    (realTokenHilbertNormedSpace (V := V))
    (realTokenHilbertNormedSpace (V := V))
    (RingHom.id ℝ) RingHomIsometric.ids

instance realContextOperatorNormedSpace :
    NormedSpace ℝ (RealContextOperator (V := V)) := by
  change NormedSpace ℝ
    (RealTokenHilbertSpace (V := V) →SL[RingHom.id ℝ]
      RealTokenHilbertSpace (V := V))
  exact ContinuousLinearMap.toNormedSpace

instance (priority := 1100) realContextOperatorModule :
    Module ℝ (RealContextOperator (V := V)) :=
  (realContextOperatorNormedSpace (V := V)).toModule

structure RealContextField where
  K : RealContextOperator (V := V)
  decayRate : ℝ
  decayRate_pos : 0 < decayRate

def realContextDerivative (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    (ψ : RealTokenHilbertSpace (V := V)) : RealContextOperator (V := V) :=
  response ψ - ctx.decayRate • ctx.K +
    (D.comp ctx.K - ctx.K.comp D)

def realContextRhs (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    (X : RealContextOperator (V := V))
    (ψ : RealTokenHilbertSpace (V := V)) : RealContextOperator (V := V) :=
  response ψ - ctx.decayRate • X + (D.comp X - X.comp D)

theorem realContextRhs_at_field (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    (ψ : RealTokenHilbertSpace (V := V)) :
    realContextRhs ctx response D ctx.K ψ =
      realContextDerivative ctx response D ψ := by
  rfl

theorem exists_realContext_state_on_Icc
    [CompleteSpace (RealContextOperator (V := V))]
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    (ψ : ℝ → RealTokenHilbertSpace (V := V))
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax)
    (X₀ : RealContextOperator (V := V))
    {a r L K : ℝ≥0}
    (hR : IsPicardLindelof
      (fun t X => realContextRhs ctx response D X (ψ t))
      t₀ X₀ a r L K)
    (hX : X₀ ∈ Metric.closedBall X₀ r) :
    ∃ X : ℝ → RealContextOperator (V := V), X t₀ = X₀ ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt X
          (realContextRhs ctx response D (X t) (ψ t))
          (Set.Icc tmin tmax) t := by
  exact IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hR hX

theorem realContext_state_hasDerivAt_interior
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    (ψ : ℝ → RealTokenHilbertSpace (V := V))
    {X : ℝ → RealContextOperator (V := V)} {a b t : ℝ}
    (hX : HasDerivWithinAt X
      (realContextRhs ctx response D (X t) (ψ t))
      (Set.Icc a b) t)
    (ht : t ∈ interior (Set.Icc a b)) :
    HasDerivAt X
      (realContextRhs ctx response D (X t) (ψ t)) t := by
  apply hX.hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨interior (Set.Icc a b), interior_subset, isOpen_interior, ht⟩

theorem realContextRhs_of_commute
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D X : RealContextOperator (V := V))
    (ψ : RealTokenHilbertSpace (V := V))
    (hcomm : D.comp X = X.comp D) :
    realContextRhs ctx response D X ψ = response ψ - ctx.decayRate • X := by
  change response ψ - ctx.decayRate • X + (D.comp X - X.comp D) = _
  rw [hcomm, sub_self]
  exact add_zero (response ψ - ctx.decayRate • X)

theorem realContextRhs_eq_zero_of_balanced_commute
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D X : RealContextOperator (V := V))
    (ψ : RealTokenHilbertSpace (V := V))
    (hcomm : D.comp X = X.comp D)
    (hbalance : response ψ = ctx.decayRate • X) :
    realContextRhs ctx response D X ψ = 0 := by
  rw [realContextRhs_of_commute ctx response D X ψ hcomm, hbalance]
  exact sub_self (ctx.decayRate • X)

structure RealContextTrajectory
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    (ψ : ℝ → RealTokenHilbertSpace (V := V)) where
  state : ℝ → RealContextOperator (V := V)
  equation : ∀ t, HasDerivAt state
    (realContextRhs ctx response D (state t) (ψ t)) t

def constant_realContextTrajectory
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    (ψ : ℝ → RealTokenHilbertSpace (V := V))
    (X : RealContextOperator (V := V))
    (heq : ∀ t, realContextRhs ctx response D X (ψ t) = 0) :
    RealContextTrajectory ctx response D ψ := by
  refine ⟨fun _ => X, ?_⟩
  intro t
  rw [heq t]
  exact hasDerivAt_const (x := t) (c := X)

def balanced_commuting_realContextTrajectory
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D X : RealContextOperator (V := V))
    (ψ : ℝ → RealTokenHilbertSpace (V := V))
    (hcomm : D.comp X = X.comp D)
    (hbalance : ∀ t, response (ψ t) = ctx.decayRate • X) :
    RealContextTrajectory ctx response D ψ :=
  constant_realContextTrajectory ctx response D ψ X
    (fun t => realContextRhs_eq_zero_of_balanced_commute
      ctx response D X (ψ t) hcomm (hbalance t))

end
end InfoGeometry.Dynamics
