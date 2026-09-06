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

/-- Legendre transform as supremum of affine supports against a dual covector. -/
noncomputable def legendre
    (ψ : Θ → ℝ)
    (η : Θ →L[ℝ] ℝ) : ℝ :=
  sSup (Set.range (fun θ : Θ => η θ - ψ θ))

/-- Fenchel conjugacy inequality (`ψ*` upper-bounds all affine supports of `ψ`). -/
def IsLegendreConjugate
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) : Prop :=
  ∀ η θ, η θ - ψ θ ≤ ψStar η

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
    (hConj : IsLegendreConjugate ψ ψStar)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    η θ ≤ ψ θ + ψStar η := by
  have h := hConj η θ
  linarith

/-- Nonnegativity of the Fenchel gap under conjugacy. -/
lemma fenchelGap_nonneg
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (hConj : IsLegendreConjugate ψ ψStar)
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

/-- Assumption package typically required to state/prove Legendre involution theorems. -/
structure LegendreInvolutionAssumptions
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) where
  conjugate : IsLegendreConjugate ψ ψStar
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

/-- Interface theorem: involution assumptions provide gradient/dual-gradient inverses. -/
theorem legendre_involution_assumption_theorem
    {ψ : Θ → ℝ}
    {ψStar : (Θ →L[ℝ] ℝ) → ℝ}
    (h : LegendreInvolutionAssumptions ψ ψStar) :
    Function.LeftInverse h.gradStar h.grad ∧
      Function.RightInverse h.gradStar h.grad := by
  exact ⟨h.left_inv, h.right_inv⟩

end InfoGeometry.Geometry
