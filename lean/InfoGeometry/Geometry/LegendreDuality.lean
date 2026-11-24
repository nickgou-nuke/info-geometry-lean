/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.MobiusDual
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
def LegendreWellPosed
    (ψ : Θ → ℝ)
    (η : Θ →L[ℝ] ℝ) : Prop :=
  (legendreSupport ψ η).Nonempty ∧
    BddAbove (legendreSupport ψ η)

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

/-!
## Projective Duality, Polar Envelopes, and Incidence Cocycles

Following Barbaresco's projective-duality formulation of the Legendre transform on an
arbitrary real normed space `Θ`:
- Primal epigraph points `(θ, z)` lift homogeneously to `(θ, z, 1) ∈ Θ × ℝ × ℝ`.
- Dual supporting hyperplanes `(η, w)` lift homogeneously to `(η, -1, -w) ∈ (Θ →L[ℝ] ℝ) × ℝ × ℝ`.
- Bilinear projective incidence is invariant under nonzero homogeneous rescaling of either
  representative, characterizes Fenchel–Young contact, and recovers the exact `sSup` Legendre
  potential as the `sInf` polar envelope of supporting projective half-spaces.
- The projective incidence defect equals `fenchelGap` and obeys a general 3-point connectivity
  cocycle, orthogonality additivity, and potential-independent triangle symplectic 2-form holonomy.
- In 1D (`Θ = ℝ`), the construction specializes to `InfoGeometry.Projective.MobiusDual`
  with exact `SL(2, ℝ)` contragredient incidence invariance on the affine chart `!![θ; 1]`.
-/

section ProjectiveLegendreDuality

/-- Bilinear projective incidence pairing between a homogeneous dual hyperplane
`H = (η, a, b)` and a homogeneous primal point `P = (θ, z, t)`. -/
def projectivePairing
    (H : (Θ →L[ℝ] ℝ) × ℝ × ℝ)
    (P : Θ × ℝ × ℝ) : ℝ :=
  H.1 P.1 + H.2.1 * P.2.1 + H.2.2 * P.2.2

/-- Projective incidence (`H ⊥ P`): vanishing of the homogeneous pairing. -/
def ProjectiveIncident
    (H : (Θ →L[ℝ] ℝ) × ℝ × ℝ)
    (P : Θ × ℝ × ℝ) : Prop :=
  projectivePairing H P = 0

lemma projectivePairing_smul_left
    (c : ℝ)
    (H : (Θ →L[ℝ] ℝ) × ℝ × ℝ)
    (P : Θ × ℝ × ℝ) :
    projectivePairing (c • H) P = c * projectivePairing H P := by
  unfold projectivePairing
  change c * H.1 P.1 + (c * H.2.1) * P.2.1 + (c * H.2.2) * P.2.2 =
    c * (H.1 P.1 + H.2.1 * P.2.1 + H.2.2 * P.2.2)
  ring

lemma projectivePairing_smul_right
    (c : ℝ)
    (H : (Θ →L[ℝ] ℝ) × ℝ × ℝ)
    (P : Θ × ℝ × ℝ) :
    projectivePairing H (c • P) = c * projectivePairing H P := by
  unfold projectivePairing
  change H.1 (c • P.1) + H.2.1 * (c * P.2.1) + H.2.2 * (c * P.2.2) =
    c * (H.1 P.1 + H.2.1 * P.2.1 + H.2.2 * P.2.2)
  rw [map_smul, smul_eq_mul]
  ring

theorem projectiveIncident_smul_left_iff
    {c : ℝ} (hc : c ≠ 0)
    (H : (Θ →L[ℝ] ℝ) × ℝ × ℝ)
    (P : Θ × ℝ × ℝ) :
    ProjectiveIncident (c • H) P ↔ ProjectiveIncident H P := by
  unfold ProjectiveIncident
  rw [projectivePairing_smul_left]
  exact mul_eq_zero_iff_left hc

theorem projectiveIncident_smul_right_iff
    {c : ℝ} (hc : c ≠ 0)
    (H : (Θ →L[ℝ] ℝ) × ℝ × ℝ)
    (P : Θ × ℝ × ℝ) :
    ProjectiveIncident H (c • P) ↔ ProjectiveIncident H P := by
  unfold ProjectiveIncident
  rw [projectivePairing_smul_right]
  exact mul_eq_zero_iff_left hc

/-- Homogeneous lift `(θ, z, 1)` of an epigraph point `(θ, z)`. -/
def primalEpigraphLift (θ : Θ) (z : ℝ) : Θ × ℝ × ℝ :=
  (θ, z, 1)

/-- Homogeneous lift `(θ, ψ θ, 1)` of a point on the graph of `ψ`. -/
def primalGraphPoint (ψ : Θ → ℝ) (θ : Θ) : Θ × ℝ × ℝ :=
  primalEpigraphLift θ (ψ θ)

/-- Homogeneous dual supporting hyperplane `(η, -1, -w)` encoding `η(θ) - z - w = 0`. -/
def dualSupportHyperplane (η : Θ →L[ℝ] ℝ) (w : ℝ) : (Θ →L[ℝ] ℝ) × ℝ × ℝ :=
  (η, -1, -w)

/-- Homogeneous dual supporting hyperplane `(η, -1, -ψ*(η))` at a dual potential `ψStar`. -/
def legendreDualHyperplane
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) (η : Θ →L[ℝ] ℝ) : (Θ →L[ℝ] ℝ) × ℝ × ℝ :=
  dualSupportHyperplane η (ψStar η)

/-- Reciprocal primal hyperplane `(θ, -1, -z)` dual to points in the dual graph. -/
def primalSupportHyperplane (θ : Θ) (z : ℝ) : Θ × ℝ × ℝ :=
  (θ, -1, -z)

/-- Homogeneous lift `(η, ψ*(η), 1)` of a point on the graph of `ψStar`. -/
def dualGraphPoint
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) (η : Θ →L[ℝ] ℝ) : (Θ →L[ℝ] ℝ) × ℝ × ℝ :=
  (η, ψStar η, 1)

/-- Reciprocal projective pairing viewing `P ∈ Θ × ℝ × ℝ` as a hyperplane acting on
`H ∈ (Θ →L[ℝ] ℝ) × ℝ × ℝ`. -/
def reciprocalProjectivePairing
    (P : Θ × ℝ × ℝ)
    (H : (Θ →L[ℝ] ℝ) × ℝ × ℝ) : ℝ :=
  H.1 P.1 + P.2.1 * H.2.1 + P.2.2 * H.2.2

theorem projectivePairing_legendreDualHyperplane_primalGraphPoint
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    projectivePairing (legendreDualHyperplane ψStar η) (primalGraphPoint ψ θ) =
      -fenchelGap ψ ψStar θ η := by
  unfold projectivePairing legendreDualHyperplane dualSupportHyperplane
    primalGraphPoint primalEpigraphLift fenchelGap
  ring

/-- Fenchel–Young contact holds iff the dual hyperplane is projectively incident to the
primal graph point. -/
theorem fenchelYoungEquality_iff_projectiveIncident
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    FenchelYoungEquality ψ ψStar θ η ↔
      ProjectiveIncident (legendreDualHyperplane ψStar η) (primalGraphPoint ψ θ) := by
  rw [fenchelYoungEquality_iff_gap_eq_zero]
  unfold ProjectiveIncident
  rw [projectivePairing_legendreDualHyperplane_primalGraphPoint]
  constructor <;> intro h <;> linarith

/-- Fenchel majorization is equivalent to the projective half-space containment of the entire
primal epigraph `{(θ, z, 1) | ψ θ ≤ z}` under every dual hyperplane `(η, -1, -ψ*(η))`. -/
theorem isFenchelMajorized_iff_epigraph_projective_halfspace
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ) :
    IsFenchelMajorized ψ ψStar ↔
      ∀ η θ z, ψ θ ≤ z →
        projectivePairing (legendreDualHyperplane ψStar η) (primalEpigraphLift θ z) ≤ 0 := by
  constructor
  · intro hMaj η θ z hz
    unfold projectivePairing legendreDualHyperplane dualSupportHyperplane primalEpigraphLift
    have h := hMaj η θ
    linarith
  · intro hHalf η θ
    have h := hHalf η θ (ψ θ) le_rfl
    unfold projectivePairing legendreDualHyperplane dualSupportHyperplane
      primalEpigraphLift at h
    linarith

/-- Offsets `w` for which the projective half-space `{P | ⟨(η, -1, -w), P⟩ ≤ 0}` contains the
entire homogeneous epigraph of `ψ`. -/
def projectiveSupportingOffsets
    (ψ : Θ → ℝ) (η : Θ →L[ℝ] ℝ) : Set ℝ :=
  {w : ℝ | ∀ θ z, ψ θ ≤ z →
    projectivePairing (dualSupportHyperplane η w) (primalEpigraphLift θ z) ≤ 0}

theorem mem_projectiveSupportingOffsets_iff_upperBounds
    (ψ : Θ → ℝ) (η : Θ →L[ℝ] ℝ) (w : ℝ) :
    w ∈ projectiveSupportingOffsets ψ η ↔ w ∈ upperBounds (legendreSupport ψ η) := by
  constructor
  · intro hw y hy
    rcases hy with ⟨θ, rfl⟩
    have h := hw θ (ψ θ) le_rfl
    unfold projectivePairing dualSupportHyperplane primalEpigraphLift at h
    linarith
  · intro hw θ z hz
    unfold projectivePairing dualSupportHyperplane primalEpigraphLift
    have h : η θ - ψ θ ≤ w := hw ⟨θ, rfl⟩
    linarith

/-- **Barbaresco Potential-Level Legendre–Projective Polar Equivalence**:
for every well-posed dual covector `η`, the `sSup` Legendre transform `legendre ψ η` equals
the `sInf` polar envelope of supporting projective hyperplane offsets. -/
theorem legendre_eq_sInf_projectiveSupportingOffsets
    (ψ : Θ → ℝ) (η : Θ →L[ℝ] ℝ)
    (hWP : LegendreWellPosed ψ η) :
    legendre ψ η = sInf (projectiveSupportingOffsets ψ η) := by
  have hset : projectiveSupportingOffsets ψ η = upperBounds (legendreSupport ψ η) := by
    ext w
    exact mem_projectiveSupportingOffsets_iff_upperBounds ψ η w
  rw [hset]
  unfold legendre
  refine le_antisymm ?_ ?_
  · refine le_csInf hWP.2 ?_
    intro w hw
    exact csSup_le hWP.1 hw
  · refine csInf_le ?_ ?_
    · rcases hWP.1 with ⟨y, hy⟩
      exact ⟨y, fun w hw => hw hy⟩
    · intro y hy
      exact le_csSup hWP.2 hy

/-- Symmetric projective point–hyperplane reciprocity: pairing the primal hyperplane
`(θ, -1, -ψ θ)` with the dual graph point `(η, ψ*(η), 1)` gives the exact same value as
pairing the dual hyperplane `(η, -1, -ψ*(η))` with the primal graph point `(θ, ψ θ, 1)`. -/
theorem projectivePairing_legendre_reciprocity
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    reciprocalProjectivePairing (primalSupportHyperplane θ (ψ θ)) (dualGraphPoint ψStar η) =
      projectivePairing (legendreDualHyperplane ψStar η) (primalGraphPoint ψ θ) := by
  unfold reciprocalProjectivePairing primalSupportHyperplane dualGraphPoint
    projectivePairing legendreDualHyperplane dualSupportHyperplane
    primalGraphPoint primalEpigraphLift
  ring

theorem projectiveIncident_legendre_reciprocity_iff
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    ProjectiveIncident (legendreDualHyperplane ψStar η) (primalGraphPoint ψ θ) ↔
      reciprocalProjectivePairing
        (primalSupportHyperplane θ (ψ θ)) (dualGraphPoint ψStar η) = 0 := by
  unfold ProjectiveIncident
  rw [projectivePairing_legendre_reciprocity]

/-- Non-negative (under majorization) projective incidence defect between primal graph point
`primalGraphPoint ψ θ` and dual supporting hyperplane `legendreDualHyperplane ψStar η`. -/
def projectiveIncidenceDefect
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) : ℝ :=
  -projectivePairing (legendreDualHyperplane ψStar η) (primalGraphPoint ψ θ)

theorem projectiveIncidenceDefect_eq_fenchelGap
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    projectiveIncidenceDefect ψ ψStar θ η = fenchelGap ψ ψStar θ η := by
  unfold projectiveIncidenceDefect
  rw [projectivePairing_legendreDualHyperplane_primalGraphPoint, neg_neg]

theorem projectiveIncidenceDefect_eq_zero_iff
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ : Θ)
    (η : Θ →L[ℝ] ℝ) :
    projectiveIncidenceDefect ψ ψStar θ η = 0 ↔
      ProjectiveIncident (legendreDualHyperplane ψStar η) (primalGraphPoint ψ θ) := by
  unfold projectiveIncidenceDefect ProjectiveIncident
  exact neg_eq_zero

/-- **Three-Point Projective Incidence Connectivity Cocycle** on an arbitrary normed space `Θ`:
relates the incidence defect `(θ₁, η₃)` to the chain through `(θ₂, η₂)` plus the canonical
primal–dual displacement pairing `(η₂ - η₃)(θ₁ - θ₂)`. -/
theorem projectiveIncidenceDefect_three_point_cocycle
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ₁ θ₂ : Θ)
    (η₂ η₃ : Θ →L[ℝ] ℝ) :
    projectiveIncidenceDefect ψ ψStar θ₁ η₃ =
      projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ -
          projectiveIncidenceDefect ψ ψStar θ₂ η₂ +
            (η₂ - η₃) (θ₁ - θ₂) := by
  simp only [projectiveIncidenceDefect_eq_fenchelGap, fenchelGap,
    sub_apply, map_sub]
  ring

/-- Generalized Pythagorean additivity of projective incidence defects under contact at the
intermediate vertex `(θ₂, η₂)` and primal–dual orthogonality `(η₂ - η₃)(θ₁ - θ₂) = 0`. -/
theorem projectiveIncidenceDefect_additive_of_orthogonal
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ₁ θ₂ : Θ)
    (η₂ η₃ : Θ →L[ℝ] ℝ)
    (hinc : ProjectiveIncident (legendreDualHyperplane ψStar η₂) (primalGraphPoint ψ θ₂))
    (horth : (η₂ - η₃) (θ₁ - θ₂) = 0) :
    projectiveIncidenceDefect ψ ψStar θ₁ η₃ =
      projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ := by
  rw [projectiveIncidenceDefect_three_point_cocycle]
  have h0 : projectiveIncidenceDefect ψ ψStar θ₂ η₂ = 0 :=
    (projectiveIncidenceDefect_eq_zero_iff ψ ψStar θ₂ η₂).2 hinc
  rw [h0, horth]
  ring

/-- **Diagonal-Referenced Triangle Holonomy**: all primal and dual potential values cancel
around a closed 3-cycle, leaving only the bilinear point–hyperplane pairings. -/
theorem projectiveIncidenceDefect_triangle_holonomy
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ₁ θ₂ θ₃ : Θ)
    (η₁ η₂ η₃ : Θ →L[ℝ] ℝ) :
    (projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ +
        projectiveIncidenceDefect ψ ψStar θ₃ η₁) -
      (projectiveIncidenceDefect ψ ψStar θ₁ η₁ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₃ η₃) =
      η₁ (θ₁ - θ₃) + η₂ (θ₂ - θ₁) + η₃ (θ₃ - θ₂) := by
  simp only [projectiveIncidenceDefect_eq_fenchelGap, fenchelGap, map_sub]
  ring

/-- **Antisymmetric Triangle Symplectic 2-Form Holonomy**: comparing the forward and reverse
cyclic projective incidence defects cancels both potentials `ψ`, `ψStar` identically and
recovers the canonical symplectic 2-form `(η₂ - η₁)(θ₃ - θ₁) - (η₃ - η₁)(θ₂ - θ₁)` on
`Θ × (Θ →L[ℝ] ℝ)`. -/
theorem projectiveIncidenceDefect_antisymm_triangle_symplectic
    (ψ : Θ → ℝ)
    (ψStar : (Θ →L[ℝ] ℝ) → ℝ)
    (θ₁ θ₂ θ₃ : Θ)
    (η₁ η₂ η₃ : Θ →L[ℝ] ℝ) :
    (projectiveIncidenceDefect ψ ψStar θ₁ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₃ +
        projectiveIncidenceDefect ψ ψStar θ₃ η₁) -
      (projectiveIncidenceDefect ψ ψStar θ₁ η₃ +
        projectiveIncidenceDefect ψ ψStar θ₃ η₂ +
        projectiveIncidenceDefect ψ ψStar θ₂ η₁) =
      (η₂ - η₁) (θ₃ - θ₁) - (η₃ - η₁) (θ₂ - θ₁) := by
  simp only [projectiveIncidenceDefect_eq_fenchelGap, fenchelGap,
    sub_apply, map_sub]
  ring

end ProjectiveLegendreDuality

end InfoGeometry.Geometry

namespace InfoGeometry.Geometry

section MobiusLegendreSpecialization

open scoped Matrix

/-- Homogeneous `ℝP¹` affine-chart lift `!![θ; 1]` in `InfoGeometry.Projective.MobiusDual`. -/
def mobiusPrimalPoint (θ : ℝ) :
    InfoGeometry.Projective.MobiusDual.ProjectivePoint ℝ :=
  !![θ; 1]

/-- Homogeneous dual `ℝP¹` line `!![η 1, -(ψ θ + ψStar η)]` whose `MobiusDual.pairing` with
`mobiusPrimalPoint θ` equals `-fenchelGap ψ ψStar θ η`. -/
def mobiusLegendreLine
    (ψ : ℝ → ℝ)
    (ψStar : (ℝ →L[ℝ] ℝ) → ℝ)
    (θ : ℝ)
    (η : ℝ →L[ℝ] ℝ) :
    InfoGeometry.Projective.MobiusDual.ProjectiveLine ℝ :=
  !![η 1, -(ψ θ + ψStar η)]

theorem mobiusDual_pairing_eq_neg_fenchelGap
    (ψ : ℝ → ℝ)
    (ψStar : (ℝ →L[ℝ] ℝ) → ℝ)
    (θ : ℝ)
    (η : ℝ →L[ℝ] ℝ) :
    InfoGeometry.Projective.MobiusDual.pairing
        (mobiusLegendreLine ψ ψStar θ η) (mobiusPrimalPoint θ) =
      -fenchelGap ψ ψStar θ η := by
  have hη : η θ = η 1 * θ := by
    calc
      η θ = η (θ • (1 : ℝ)) := by simp
      _ = θ • η 1 := map_smul η θ (1 : ℝ)
      _ = η 1 * θ := by simp [smul_eq_mul, mul_comm]
  simp [InfoGeometry.Projective.MobiusDual.pairing, mobiusLegendreLine, mobiusPrimalPoint,
    fenchelGap, hη]
  ring

/-- Exact 1D `SL(2, ℝ)` contragredient invariance of Fenchel–Young projective incidence
via `InfoGeometry.Projective.MobiusDual.contragredient_pairing_invariant`. -/
theorem fenchelYoungEquality_iff_mobiusDual_contragredient_incident
    (ψ : ℝ → ℝ)
    (ψStar : (ℝ →L[ℝ] ℝ) → ℝ)
    (θ : ℝ)
    (η : ℝ →L[ℝ] ℝ)
    (A : InfoGeometry.Projective.MobiusDual.SL2 ℝ) :
    FenchelYoungEquality ψ ψStar θ η ↔
      InfoGeometry.Projective.MobiusDual.pairing
        (InfoGeometry.Projective.MobiusDual.actLine A (mobiusLegendreLine ψ ψStar θ η))
        (InfoGeometry.Projective.MobiusDual.actPoint A (mobiusPrimalPoint θ)) = 0 := by
  rw [InfoGeometry.Projective.MobiusDual.contragredient_pairing_invariant,
    mobiusDual_pairing_eq_neg_fenchelGap,
    fenchelYoungEquality_iff_gap_eq_zero]
  constructor <;> intro h <;> linarith

end MobiusLegendreSpecialization

end InfoGeometry.Geometry
