import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic.Linarith

/-!
# Legendre Duality

Dedicated structural API for Legendre/Fenchel duality in Hessian-style settings.
-/

namespace InfoGeometry.Geometry

variable {Θ : Type _}
variable [NormedAddCommGroup Θ]
variable [NormedSpace ℝ Θ]

/-- Affine-support set used in the Legendre/Fenchel supremum. -/
def legendreSupport
    (ψ : Θ → ℝ)
    (η : Θ →L[ℝ] ℝ) : Set ℝ :=
  Set.range (fun θ : Θ => η θ - ψ θ)

/-- Legendre transform as supremum of affine supports against a dual covector. -/
noncomputable def legendre
    (ψ : Θ → ℝ)
    (η : Θ →L[ℝ] ℝ) : ℝ :=
  sSup (legendreSupport ψ η)

/-- Well-posedness assumptions for the real-valued `sSup` Legendre transform. -/
structure LegendreWellPosed
    (ψ : Θ → ℝ)
    (η : Θ →L[ℝ] ℝ) : Prop where
  nonempty : (legendreSupport ψ η).Nonempty
  bddAbove : BddAbove (legendreSupport ψ η)

lemma le_legendre_of_bddAbove
    (ψ : Θ → ℝ)
    (η : Θ →L[ℝ] ℝ)
    (hb : BddAbove (legendreSupport ψ η))
    (θ : Θ) :
    η θ - ψ θ ≤ legendre ψ η := by
  exact le_csSup hb ⟨θ, rfl⟩

/-- Fenchel majorization (`ψ*` upper-bounds all affine supports of `ψ`). -/
def IsFenchelMajorized
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) : Prop :=
  ∀ η θ, η θ - ψ θ ≤ ψStar η

/-- Exact Fenchel conjugacy via equality with the support supremum. -/
def IsFenchelConjugate
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) : Prop :=
  ∀ η, ψStar η = legendre ψ η

/--
Backward-compatible alias.
This corresponds to Fenchel majorization, not necessarily exact conjugacy.
-/
abbrev IsLegendreConjugate
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) : Prop :=
  IsFenchelMajorized ψ ψStar

lemma IsFenchelConjugate.isFenchelMajorized
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (hConj : IsFenchelConjugate ψ ψStar)
    (hBdd : ∀ η, BddAbove (legendreSupport ψ η)) :
    IsFenchelMajorized ψ ψStar := by
  intro η θ
  have hle : η θ - ψ θ ≤ legendre ψ η :=
    le_legendre_of_bddAbove ψ η (hBdd η) θ
  simpa [hConj η] using hle

/-- Fenchel gap associated to a primal/dual pair. -/
def fenchelGap
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) : ℝ :=
  ψ θ + ψStar η - η θ

/-- Fenchel-Young inequality from conjugacy. -/
lemma fenchelYoung_ineq
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (hConj : IsFenchelMajorized ψ ψStar)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    η θ ≤ ψ θ + ψStar η := by
  have h := hConj η θ
  linarith

/-- Nonnegativity of the Fenchel gap under conjugacy. -/
lemma fenchelGap_nonneg
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (hConj : IsFenchelMajorized ψ ψStar)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    0 ≤ fenchelGap ψ ψStar θ η := by
  unfold fenchelGap
  have h := hConj η θ
  linarith

/-- Equality case in Fenchel-Young at a point `(θ,η)`. -/
def FenchelYoungEquality
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) : Prop :=
  ψ θ + ψStar η = η θ

lemma fenchelYoungEquality_iff_gap_eq_zero
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    FenchelYoungEquality ψ ψStar θ η ↔ fenchelGap ψ ψStar θ η = 0 := by
  constructor
  · intro hEq
    unfold FenchelYoungEquality at hEq
    unfold fenchelGap
    linarith
  · intro hGap
    unfold FenchelYoungEquality
    unfold fenchelGap at hGap
    linarith

lemma fenchelYoungEquality_of_dual_value
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ)
    (h : ψStar η = η θ - ψ θ) :
    FenchelYoungEquality ψ ψStar θ η := by
  unfold FenchelYoungEquality
  linarith

lemma dual_value_of_fenchelYoungEquality
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ)
    (hEq : FenchelYoungEquality ψ ψStar θ η) :
    ψStar η = η θ - ψ θ := by
  unfold FenchelYoungEquality at hEq
  linarith

/-- Explicit involution interface from inverse gradient maps. -/
theorem legendre_involution_of_inverse_maps
    (grad : Θ → (Θ →L[ℝ] ℝ))
    (gradStar : (Θ →L[ℝ] ℝ) → Θ)
    (hLeft : Function.LeftInverse gradStar grad)
    (hRight : Function.RightInverse gradStar grad) :
    Function.LeftInverse gradStar grad ∧
      Function.RightInverse gradStar grad := by
  exact ⟨hLeft, hRight⟩

/-- Explicit Fenchel-Young equality along `grad` implies zero Fenchel gap along `grad`. -/
theorem fenchelGap_zero_along_grad_of_fenchelYoung
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (grad : Θ → (Θ →L[ℝ] ℝ))
    (hFY : ∀ θ : Θ, FenchelYoungEquality ψ ψStar θ (grad θ)) :
    ∀ θ : Θ, fenchelGap ψ ψStar θ (grad θ) = 0 := by
  intro θ
  exact (fenchelYoungEquality_iff_gap_eq_zero ψ ψStar θ (grad θ)).1 (hFY θ)

/-- Explicit Fenchel-Young equality along `grad` gives the dual value formula along `grad`. -/
theorem dual_value_along_grad_of_fenchelYoung
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (grad : Θ → (Θ →L[ℝ] ℝ))
    (hFY : ∀ θ : Θ, FenchelYoungEquality ψ ψStar θ (grad θ)) :
    ∀ θ : Θ, ψStar (grad θ) = grad θ θ - ψ θ := by
  intro θ
  exact dual_value_of_fenchelYoungEquality ψ ψStar θ (grad θ) (hFY θ)

/-- Assumption package typically required to state/prove Legendre involution theorems. -/
structure LegendreInvolutionAssumptions
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) where
  conjugate : IsFenchelMajorized ψ ψStar
  diff : Differentiable ℝ ψ
  grad : Θ → (Θ →L[ℝ] ℝ)
  gradStar : (Θ →L[ℝ] ℝ) → Θ
  grad_eq_fderiv : ∀ θ, grad θ = fderiv ℝ ψ θ
  left_inv : Function.LeftInverse gradStar grad
  right_inv : Function.RightInverse gradStar grad
  fenchelYoung_along_grad :
    ∀ θ, FenchelYoungEquality ψ ψStar θ (grad θ)

lemma LegendreInvolutionAssumptions.fenchelYoung_eq
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (h : LegendreInvolutionAssumptions ψ ψStar)
    (θ : Θ) :
    FenchelYoungEquality ψ ψStar θ (h.grad θ) :=
  h.fenchelYoung_along_grad θ

lemma LegendreInvolutionAssumptions.fenchelGap_eq_zero_along_grad
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (h : LegendreInvolutionAssumptions ψ ψStar)
    (θ : Θ) :
    fenchelGap ψ ψStar θ (h.grad θ) = 0 := by
  exact
    (fenchelYoungEquality_iff_gap_eq_zero ψ ψStar θ (h.grad θ)).1
      (h.fenchelYoung_along_grad θ)

lemma LegendreInvolutionAssumptions.dual_value_along_grad
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (h : LegendreInvolutionAssumptions ψ ψStar)
    (θ : Θ) :
    ψStar (h.grad θ) = h.grad θ θ - ψ θ := by
  exact dual_value_of_fenchelYoungEquality ψ ψStar θ (h.grad θ)
    (h.fenchelYoung_along_grad θ)

/-- Interface theorem: involution assumptions provide gradient/dual-gradient inverses. -/
theorem legendre_involution_assumption_theorem
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (h : LegendreInvolutionAssumptions ψ ψStar) :
    Function.LeftInverse h.gradStar h.grad ∧
      Function.RightInverse h.gradStar h.grad := by
  exact ⟨h.left_inv, h.right_inv⟩

/-- Stronger interface: involution assumptions imply zero Fenchel gap along `grad`. -/
theorem legendre_involution_gap_theorem
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (h : LegendreInvolutionAssumptions ψ ψStar) :
    ∀ θ, fenchelGap ψ ψStar θ (h.grad θ) = 0 :=
  h.fenchelGap_eq_zero_along_grad

end InfoGeometry.Geometry
