import InfoGeometry.GrandCanonical.Core
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Grand Canonical Response Matrix

Two-parameter thermodynamic Hessian / susceptibility surface for the finite
grand-canonical model.
-/

namespace InfoGeometry.GrandCanonical

variable {α : Type*} [Fintype α] [Nonempty α]

/-- β-slice of the grand-canonical potential at fixed chemical potential. -/
noncomputable abbrev potentialBetaSlice
    (params : GrandCanonicalTwoParam α) (μ : ℝ) : ℝ → ℝ :=
  fun β => potentialGC params β μ

/-- μ-slice of the grand-canonical potential at fixed inverse temperature. -/
noncomputable abbrev potentialMuSlice
    (params : GrandCanonicalTwoParam α) (β : ℝ) : ℝ → ℝ :=
  fun μ => potentialGC params β μ

/-- First β-response: `∂_β Φ(β, μ)`. -/
noncomputable abbrev betaResponse
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  deriv (potentialBetaSlice params μ) β

/-- First μ-response: `∂_μ Φ(β, μ)`. -/
noncomputable abbrev muResponse
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  deriv (potentialMuSlice params β) μ

/-- Second β-derivative: `∂²_{ββ} Φ(β, μ)`. -/
noncomputable abbrev betaHessian
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  deriv (fun t => betaResponse params t μ) β

/-- Second μ-derivative: `∂²_{μμ} Φ(β, μ)`. -/
noncomputable abbrev muHessian
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  deriv (fun t => muResponse params β t) μ

/-- Mixed derivative in the order `∂_μ ∂_β Φ(β, μ)`. -/
noncomputable abbrev betaMuHessian
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  deriv (fun t => betaResponse params β t) μ

/-- Mixed derivative in the order `∂_β ∂_μ Φ(β, μ)`. -/
noncomputable abbrev muBetaHessian
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ℝ :=
  deriv (fun t => muResponse params t μ) β

/-- Thermodynamic response / susceptibility matrix in `(β, μ)` coordinates. -/
structure ResponseMatrix2 where
  betaBeta : ℝ
  betaMu   : ℝ
  muBeta   : ℝ
  muMu     : ℝ

namespace ResponseMatrix2

/-- Symmetry of the thermodynamic Hessian. -/
def Symmetric (M : ResponseMatrix2) : Prop :=
  M.betaMu = M.muBeta

/-- Determinant of the `2×2` response matrix. -/
def det (M : ResponseMatrix2) : ℝ :=
  M.betaBeta * M.muMu - M.betaMu * M.muBeta

/-- Positive semidefinite interface for the `2×2` thermodynamic metric. -/
def PositiveSemidefinite (M : ResponseMatrix2) : Prop :=
  0 ≤ M.betaBeta ∧ 0 ≤ M.muMu ∧ 0 ≤ M.det

end ResponseMatrix2

/-- Canonical thermodynamic response matrix at `(β, μ)`. -/
noncomputable def responseMatrix
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : ResponseMatrix2 where
  betaBeta := betaHessian params β μ
  betaMu   := betaMuHessian params β μ
  muBeta   := muBetaHessian params β μ
  muMu     := muHessian params β μ

/-- Two-parameter spinodal locus: degeneracy of the response matrix. -/
def Spinodal2D
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) : Prop :=
  (responseMatrix params β μ).det = 0

/-- First β-response is the negative shifted mean. -/
lemma betaResponse_eq_neg_meanShift
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    betaResponse params β μ = -meanShift params β μ := by
  simpa [betaResponse, potentialBetaSlice] using
    potentialGC_deriv_beta_eq_neg_meanShift params β μ

/-- First μ-response is `β` times the mean number. -/
lemma muResponse_eq_beta_meanNumber
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    muResponse params β μ = β * meanNumber params β μ := by
  simpa [muResponse, potentialMuSlice] using
    potentialGC_deriv_mu_eq_beta_meanNumber params β μ

omit [Nonempty α] in
/-- Symmetry interface once the mixed-partial theorem is supplied downstream. -/
lemma responseMatrix_symmetric
    (params : GrandCanonicalTwoParam α) (β μ : ℝ)
    (hMixed : betaMuHessian params β μ = muBetaHessian params β μ) :
    (responseMatrix params β μ).Symmetric :=
  hMixed

omit [Nonempty α] in
/-- PSD interface once diagonal nonnegativity and determinant nonnegativity are supplied. -/
lemma responseMatrix_positiveSemidefinite
    (params : GrandCanonicalTwoParam α) (β μ : ℝ)
    (hββ : 0 ≤ betaHessian params β μ)
    (hμμ : 0 ≤ muHessian params β μ)
    (hdet : 0 ≤ (responseMatrix params β μ).det) :
    (responseMatrix params β μ).PositiveSemidefinite :=
  ⟨hββ, hμμ, hdet⟩

omit [Nonempty α] in
/-- The two-parameter spinodal locus is exactly determinant degeneracy. -/
lemma spinodal2D_iff_det_eq_zero
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    Spinodal2D params β μ ↔ (responseMatrix params β μ).det = 0 :=
  Iff.rfl

end InfoGeometry.GrandCanonical
