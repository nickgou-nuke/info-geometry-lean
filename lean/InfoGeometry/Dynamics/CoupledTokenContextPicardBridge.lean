import Mathlib.Analysis.ODE.PicardLindelof
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Dynamics.RealifiedContinuousContextBackreaction
import InfoGeometry.Dynamics.TokenPiLpBridge

/-!
# Coupled token/context local evolution

This owner forms the genuine product carrier from the existing real token and
context-operator carriers.  The Picard--Lindelöf condition is an explicit
hypothesis on the concrete coupled right-hand side; no regularity of a
nonlinear response is inferred from its name.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

open scoped NNReal

abbrev CoupledTokenContextState :=
  RealTokenHilbertSpace (V := V) × RealContextOperator (V := V)

def realTokenCoordinateMap :
    RealTokenHilbertSpace (V := V) →ₗ[ℝ]
      ((V × Fin 2) × Fin 2 → ℝ) where
  toFun ψ p := if p.2 = 0 then (ψ p.1).re else (ψ p.1).im
  map_add' ψ φ := by
    funext p
    by_cases h : p.2 = 0
    · simp [h]
      change (ψ p.1 + φ p.1).re = _
      simp
    · simp [h]
      change (ψ p.1 + φ p.1).im = _
      simp
  map_smul' c ψ := by
    funext p
    by_cases h : p.2 = 0
    · simp [h]
      change (c • (ψ p.1)).re = _
      simp
    · simp [h]
      change (c • (ψ p.1)).im = _
      simp

theorem realTokenCoordinateMap_injective :
    Function.Injective (realTokenCoordinateMap (V := V)) := by
  intro ψ φ h
  funext p
  apply Complex.ext
  · simpa using congr_fun h (p, 0)
  · simpa using congr_fun h (p, 1)

instance realTokenFiniteDimensional :
    FiniteDimensional ℝ (RealTokenHilbertSpace (V := V)) :=
  FiniteDimensional.of_injective
    (realTokenCoordinateMap (V := V))
    (realTokenCoordinateMap_injective (V := V))

def realTokenToPiLpLinear :
    RealTokenHilbertSpace (V := V) →ₗ[ℝ] TokenPiLpSpace V where
  toFun ψ := tokenToPiLp ψ
  map_add' ψ φ := by
    rfl
  map_smul' c ψ := by
    rfl

noncomputable def realTokenToPiLp :
    RealTokenHilbertSpace (V := V) →L[ℝ] TokenPiLpSpace V :=
  { toLinearMap := realTokenToPiLpLinear (V := V)
    cont := LinearMap.continuous_of_finiteDimensional _ }

def coupledTokenContextRhs
    (tokenRhs : ℝ → CoupledTokenContextState (V := V) →
      RealTokenHilbertSpace (V := V))
    (contextRhs : ℝ → CoupledTokenContextState (V := V) →
      RealContextOperator (V := V))
    (t : ℝ) (x : CoupledTokenContextState (V := V)) :
    CoupledTokenContextState (V := V) :=
  (tokenRhs t x, contextRhs t x)

@[simp] theorem coupledTokenContextRhs_fst
    (tokenRhs : ℝ → CoupledTokenContextState (V := V) →
      RealTokenHilbertSpace (V := V))
    (contextRhs : ℝ → CoupledTokenContextState (V := V) →
      RealContextOperator (V := V)) (t : ℝ)
    (x : CoupledTokenContextState (V := V)) :
    (coupledTokenContextRhs tokenRhs contextRhs t x).1 = tokenRhs t x := rfl

@[simp] theorem coupledTokenContextRhs_snd
    (tokenRhs : ℝ → CoupledTokenContextState (V := V) →
      RealTokenHilbertSpace (V := V))
    (contextRhs : ℝ → CoupledTokenContextState (V := V) →
      RealContextOperator (V := V)) (t : ℝ)
    (x : CoupledTokenContextState (V := V)) :
    (coupledTokenContextRhs tokenRhs contextRhs t x).2 = contextRhs t x := rfl

theorem coupledTokenContextRhs_eq_zero_iff
    (tokenRhs : ℝ → CoupledTokenContextState (V := V) →
      RealTokenHilbertSpace (V := V))
    (contextRhs : ℝ → CoupledTokenContextState (V := V) →
      RealContextOperator (V := V)) (t : ℝ)
    (x : CoupledTokenContextState (V := V)) :
    coupledTokenContextRhs tokenRhs contextRhs t x = 0 ↔
      tokenRhs t x = 0 ∧ contextRhs t x = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨ht, hc⟩
    exact Prod.ext ht hc

/-! The concrete product RHS obtained from the repository's realified token
    generator and real context backreaction owners. -/
def tokenContextRhs
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    (t : ℝ) (x : CoupledTokenContextState (V := V)) :
    CoupledTokenContextState (V := V) :=
  coupledTokenContextRhs
    (fun _ x => realifiedTotalTokenGenerator gen x.1)
    (fun _ x => realContextRhs ctx response D x.2 x.1)
    t x

theorem tokenContext_tokenToPiLp_hasDerivAt
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)} {t : ℝ}
    (hx : HasDerivAt x (tokenContextRhs gen ctx response D t (x t)) t) :
    HasDerivAt (fun τ => realTokenToPiLp (V := V) ((x τ).1))
      (realTokenToPiLp (V := V) (realifiedTotalTokenGenerator gen (x t).1)) t := by
  simpa [Function.comp_def, tokenContextRhs] using
    (realTokenToPiLp (V := V)).hasFDerivAt.comp_hasDerivAt_of_eq t hx.fst rfl

theorem tokenContext_tokenToPiLp_equation
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)} {t : ℝ}
    (hx : HasDerivAt x (tokenContextRhs gen ctx response D t (x t)) t) :
    HasDerivAt (fun τ => realTokenToPiLp (V := V) ((x τ).1))
      (transportTokenGeneratorReal gen
        (realTokenToPiLp (V := V) ((x t).1))) t := by
  have h := tokenContext_tokenToPiLp_hasDerivAt gen ctx response D hx
  convert h using 1

def tokenComponentPiLpTrajectory
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)}
    (hx : ∀ t, HasDerivAt x
      (tokenContextRhs gen ctx response D t (x t)) t) :
    TokenPiLpTrajectory (transportTokenGeneratorReal gen) where
  state := fun t => realTokenToPiLp (V := V) ((x t).1)
  equation := fun t => tokenContext_tokenToPiLp_equation
    gen ctx response D (hx t)

@[simp] theorem tokenComponentPiLpTrajectory_state
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)}
    (hx : ∀ t, HasDerivAt x
      (tokenContextRhs gen ctx response D t (x t)) t) (t : ℝ) :
    (tokenComponentPiLpTrajectory gen ctx response D hx).state t =
      realTokenToPiLp (V := V) ((x t).1) := rfl

theorem tokenComponentPiLpTrajectory_norm_sq_deriv_eq
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)}
    (hx : ∀ t, HasDerivAt x
      (tokenContextRhs gen ctx response D t (x t)) t) (t : ℝ) :
    deriv (fun τ => ‖(tokenComponentPiLpTrajectory gen ctx response D hx).state τ‖ ^ 2) t =
      2 * inner ℝ
        ((tokenComponentPiLpTrajectory gen ctx response D hx).state t)
        (transportTokenGeneratorReal gen
          ((tokenComponentPiLpTrajectory gen ctx response D hx).state t)) := by
  exact (tokenPiLpTrajectory_norm_sq_hasDerivAt
    (transportTokenGeneratorReal gen)
    (tokenComponentPiLpTrajectory gen ctx response D hx) t).deriv

theorem tokenComponentPiLpTrajectory_norm_sq_deriv_nonpos
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)}
    (hx : ∀ t, HasDerivAt x
      (tokenContextRhs gen ctx response D t (x t)) t)
    (hdissipative : ∀ ψ, inner ℝ ψ
      (transportTokenGeneratorReal gen ψ) ≤ 0) (t : ℝ) :
    deriv (fun τ => ‖(tokenComponentPiLpTrajectory gen ctx response D hx).state τ‖ ^ 2) t ≤ 0 := by
  exact tokenPiLpTrajectory_norm_sq_deriv_nonpos
    (transportTokenGeneratorReal gen) hdissipative
    (tokenComponentPiLpTrajectory gen ctx response D hx) t

theorem tokenComponentPiLpTrajectory_norm_sq_deriv_eq_zero_iff
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)}
    (hx : ∀ t, HasDerivAt x
      (tokenContextRhs gen ctx response D t (x t)) t) (t : ℝ) :
    deriv (fun τ => ‖(tokenComponentPiLpTrajectory gen ctx response D hx).state τ‖ ^ 2) t = 0 ↔
      inner ℝ
        ((tokenComponentPiLpTrajectory gen ctx response D hx).state t)
        (transportTokenGeneratorReal gen
          ((tokenComponentPiLpTrajectory gen ctx response D hx).state t)) = 0 := by
  rw [tokenComponentPiLpTrajectory_norm_sq_deriv_eq gen ctx response D hx t]
  constructor <;> intro h <;> linarith

@[simp] theorem tokenContextRhs_fst
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V)) (t : ℝ)
    (x : CoupledTokenContextState (V := V)) :
    (tokenContextRhs gen ctx response D t x).1 =
      realifiedTotalTokenGenerator gen x.1 := rfl

@[simp] theorem tokenContextRhs_snd
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V)) (t : ℝ)
    (x : CoupledTokenContextState (V := V)) :
    (tokenContextRhs gen ctx response D t x).2 =
      realContextRhs ctx response D x.2 x.1 := rfl

theorem tokenContextRhs_eq_zero_iff
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V)) (t : ℝ)
    (x : CoupledTokenContextState (V := V)) :
    tokenContextRhs gen ctx response D t x = 0 ↔
      realifiedTotalTokenGenerator gen x.1 = 0 ∧
      realContextRhs ctx response D x.2 x.1 = 0 := by
  exact coupledTokenContextRhs_eq_zero_iff _ _ t x

theorem tokenContext_token_component_hasDerivAt
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)} {t : ℝ}
    (hx : HasDerivAt x (tokenContextRhs gen ctx response D t (x t)) t) :
    HasDerivAt (fun τ => (x τ).1)
      (realifiedTotalTokenGenerator gen (x t).1) t := by
  simpa using hx.fst

/-- The context component of a coupled trajectory satisfies its native
    context equation.  This is the product-projection counterpart of
    `tokenContext_token_component_hasDerivAt`; no regularity of the response
    map is inferred here. -/
theorem tokenContext_context_component_hasDerivAt
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {x : ℝ → CoupledTokenContextState (V := V)} {t : ℝ}
    (hx : HasDerivAt x (tokenContextRhs gen ctx response D t (x t)) t) :
    HasDerivAt (fun τ => (x τ).2)
      (realContextRhs ctx response D (x t).2 (x t).1) t := by
  simpa using hx.snd

theorem exists_coupledTokenContext_state_on_Icc
    [CompleteSpace (RealTokenHilbertSpace (V := V))]
    [CompleteSpace (RealContextOperator (V := V))]
    (tokenRhs : ℝ → CoupledTokenContextState (V := V) →
      RealTokenHilbertSpace (V := V))
    (contextRhs : ℝ → CoupledTokenContextState (V := V) →
      RealContextOperator (V := V))
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax)
    (x₀ : CoupledTokenContextState (V := V))
    {a r L K : ℝ≥0}
    (hR : IsPicardLindelof
      (fun t x => coupledTokenContextRhs tokenRhs contextRhs t x)
      t₀ x₀ a r L K)
    (hx : x₀ ∈ Metric.closedBall x₀ r) :
    ∃ x : ℝ → CoupledTokenContextState (V := V), x t₀ = x₀ ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt x
          (coupledTokenContextRhs tokenRhs contextRhs t (x t))
          (Set.Icc tmin tmax) t := by
  exact IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hR hx

theorem exists_tokenContext_state_on_Icc
    [CompleteSpace (RealTokenHilbertSpace (V := V))]
    [CompleteSpace (RealContextOperator (V := V))]
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax)
    (x₀ : CoupledTokenContextState (V := V))
    {a r L K : ℝ≥0}
    (hR : IsPicardLindelof
      (fun t x => tokenContextRhs gen ctx response D t x)
      t₀ x₀ a r L K)
    (hx : x₀ ∈ Metric.closedBall x₀ r) :
    ∃ x : ℝ → CoupledTokenContextState (V := V), x t₀ = x₀ ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt x
          (tokenContextRhs gen ctx response D t (x t))
          (Set.Icc tmin tmax) t := by
  exact exists_coupledTokenContext_state_on_Icc
    (fun _ x => realifiedTotalTokenGenerator gen x.1)
    (fun _ x => realContextRhs ctx response D x.2 x.1)
    t₀ x₀ hR hx

theorem exists_constant_coupledTokenContext_state
    (tokenRhs : ℝ → CoupledTokenContextState (V := V) →
      RealTokenHilbertSpace (V := V))
    (contextRhs : ℝ → CoupledTokenContextState (V := V) →
      RealContextOperator (V := V))
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax)
    (x₀ : CoupledTokenContextState (V := V))
    (heq : ∀ t, coupledTokenContextRhs tokenRhs contextRhs t x₀ = 0) :
    ∃ x : ℝ → CoupledTokenContextState (V := V), x t₀ = x₀ ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt x
          (coupledTokenContextRhs tokenRhs contextRhs t (x t))
          (Set.Icc tmin tmax) t := by
  refine ⟨fun _ => x₀, rfl, ?_⟩
  intro t ht
  simpa [heq t] using
    (hasDerivAt_const (x := t) (c := x₀)).hasDerivWithinAt

theorem exists_constant_tokenContext_equilibrium
    (gen : TokenGenerator (V := V))
    (ctx : RealContextField (V := V))
    (response : RealTokenHilbertSpace (V := V) → RealContextOperator (V := V))
    (D : RealContextOperator (V := V))
    {tmin tmax : ℝ} (t₀ : Set.Icc tmin tmax)
    (ψ₀ : RealTokenHilbertSpace (V := V))
    (X₀ : RealContextOperator (V := V))
    (hH : gen.H ψ₀ = 0) (hGamma : gen.Gamma ψ₀ = 0)
    (hcomm : D.comp X₀ = X₀.comp D)
    (hbalance : response ψ₀ = ctx.decayRate • X₀) :
    ∃ x : ℝ → CoupledTokenContextState (V := V),
      x t₀ = (ψ₀, X₀) ∧
      ∀ t ∈ Set.Icc tmin tmax,
        HasDerivWithinAt x
          (tokenContextRhs gen ctx response D t (x t))
          (Set.Icc tmin tmax) t := by
  apply exists_constant_coupledTokenContext_state
  intro t
  apply (tokenContextRhs_eq_zero_iff gen ctx response D t (ψ₀, X₀)).2
  constructor
  · exact realifiedTotalTokenGenerator_eq_zero_of_components_eq_zero gen ψ₀ hH hGamma
  · exact realContextRhs_eq_zero_of_balanced_commute ctx response D X₀ ψ₀ hcomm hbalance

end
end InfoGeometry.Dynamics
