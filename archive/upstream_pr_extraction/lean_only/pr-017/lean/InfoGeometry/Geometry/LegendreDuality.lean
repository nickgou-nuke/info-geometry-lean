import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Convex.Function
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

lemma primal_value_of_fenchelYoungEquality
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ)
    (hEq : FenchelYoungEquality ψ ψStar θ η) :
    ψ θ = η θ - ψStar η := by
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

section ConcreteLegendre

variable {ψ : Θ → ℝ}
variable {ψStar : (Θ →L[ℝ] ℝ) → ℝ}

/-- Exact conjugacy with bounded support implies Fenchel majorization. -/
theorem isFenchelMajorized_of_concrete
    (hConj : IsFenchelConjugate ψ ψStar)
    (hSupport : ∀ η, BddAbove (legendreSupport ψ η)) :
    IsFenchelMajorized ψ ψStar :=
  hConj.isFenchelMajorized (hBdd := hSupport)

/-- Exact dual-value equality implies Fenchel-Young equality along `fderiv`. -/
theorem fenchelYoung_along_fderiv_of_concrete
    (hDualValue :
      ∀ θ, ψStar (fderiv ℝ ψ θ) = fderiv ℝ ψ θ θ - ψ θ) :
    ∀ θ, FenchelYoungEquality ψ ψStar θ (fderiv ℝ ψ θ) := by
  intro θ
  exact fenchelYoungEquality_of_dual_value ψ ψStar θ (fderiv ℝ ψ θ)
    (hDualValue θ)

/-- Zero Fenchel gap along `fderiv` from explicit dual-value equality. -/
theorem fenchelGap_eq_zero_along_fderiv_of_concrete
    (hDualValue :
      ∀ θ, ψStar (fderiv ℝ ψ θ) = fderiv ℝ ψ θ θ - ψ θ) :
    ∀ θ, fenchelGap ψ ψStar θ (fderiv ℝ ψ θ) = 0 := by
  intro θ
  exact
    (fenchelYoungEquality_iff_gap_eq_zero ψ ψStar θ (fderiv ℝ ψ θ)).1
      ((fenchelYoung_along_fderiv_of_concrete
        (ψ := ψ) (ψStar := ψStar) hDualValue) θ)

end ConcreteLegendre

end InfoGeometry.Geometry
