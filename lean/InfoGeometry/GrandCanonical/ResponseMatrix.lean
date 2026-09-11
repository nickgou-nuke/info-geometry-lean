import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- Extensionality for finite response packets. -/
@[ext]
theorem ext {M N : ResponseMatrix2}
    (hββ : M.betaBeta = N.betaBeta)
    (hβμ : M.betaMu = N.betaMu)
    (hμβ : M.muBeta = N.muBeta)
    (hμμ : M.muMu = N.muMu) :
    M = N := by
  cases M
  cases N
  simp_all

/-- Symmetry of the thermodynamic Hessian. -/
def Symmetric (M : ResponseMatrix2) : Prop :=
  M.betaMu = M.muBeta

/-- Determinant of the `2×2` response matrix. -/
def det (M : ResponseMatrix2) : ℝ :=
  M.betaBeta * M.muMu - M.betaMu * M.muBeta

/-- Positive semidefinite interface for the `2×2` thermodynamic metric. -/
def PositiveSemidefinite (M : ResponseMatrix2) : Prop :=
  0 ≤ M.betaBeta ∧ 0 ≤ M.muMu ∧ 0 ≤ M.det

/-- Identity response matrix for the finite `2×2` channel. -/
def identityMetric : ResponseMatrix2 where
  betaBeta := 1
  betaMu := 0
  muBeta := 0
  muMu := 1

/-- Matrix product for finite `2×2` response packets. -/
def compose (A B : ResponseMatrix2) : ResponseMatrix2 where
  betaBeta := A.betaBeta * B.betaBeta + A.betaMu * B.muBeta
  betaMu := A.betaBeta * B.betaMu + A.betaMu * B.muMu
  muBeta := A.muBeta * B.betaBeta + A.muMu * B.muBeta
  muMu := A.muBeta * B.betaMu + A.muMu * B.muMu

/--
Explicit inverse response matrix on the non-spinodal locus `det ≠ 0`.

This is the finite algebraic inverse-metric surface.  It is not the smooth
statement `Hess(S) = Fisher⁻¹`; it is the concrete inverse of the finite
Fisher/Onsager response packet.
-/
noncomputable def inverseMetric (M : ResponseMatrix2) : ResponseMatrix2 where
  betaBeta := M.muMu / M.det
  betaMu := -M.betaMu / M.det
  muBeta := -M.muBeta / M.det
  muMu := M.betaBeta / M.det

/-- The inverse of a symmetric finite response matrix is symmetric. -/
lemma inverseMetric_symmetric {M : ResponseMatrix2}
    (hSym : M.Symmetric) :
    M.inverseMetric.Symmetric := by
  dsimp [inverseMetric, Symmetric] at hSym ⊢
  rw [hSym]

/-- Right inverse law for the finite response metric on `det ≠ 0`. -/
lemma compose_inverseMetric_of_det_ne_zero
    {M : ResponseMatrix2} (hdet : M.det ≠ 0) :
    M.compose M.inverseMetric = identityMetric := by
  cases M with
  | mk a b c d =>
    have hΔ : a * d - b * c ≠ 0 := by
      simpa [det] using hdet
    apply ResponseMatrix2.ext
    · dsimp [compose, inverseMetric, identityMetric, det]
      field_simp [hΔ]
      ring
    · dsimp [compose, inverseMetric, identityMetric, det]
      field_simp [hΔ]
      ring
    · dsimp [compose, inverseMetric, identityMetric, det]
      field_simp [hΔ]
      ring
    · dsimp [compose, inverseMetric, identityMetric, det]
      calc
        c * (-b / (a * d - b * c)) + d * (a / (a * d - b * c))
            = (a * d - c * b) / (a * d - b * c) := by
              field_simp [hΔ]
              ring
        _ = (a * d - b * c) / (a * d - b * c) := by ring
        _ = 1 := by
              field_simp [hΔ]

/-- Left inverse law for the finite response metric on `det ≠ 0`. -/
lemma inverseMetric_compose_of_det_ne_zero
    {M : ResponseMatrix2} (hdet : M.det ≠ 0) :
    M.inverseMetric.compose M = identityMetric := by
  cases M with
  | mk a b c d =>
    have hΔ : a * d - b * c ≠ 0 := by
      simpa [det] using hdet
    apply ResponseMatrix2.ext
    · dsimp [compose, inverseMetric, identityMetric, det]
      calc
        (d / (a * d - b * c)) * a + (-b / (a * d - b * c)) * c
            = (d * a - b * c) / (a * d - b * c) := by
              field_simp [hΔ]
              ring
        _ = (a * d - b * c) / (a * d - b * c) := by ring
        _ = 1 := by
              field_simp [hΔ]
    · dsimp [compose, inverseMetric, identityMetric, det]
      field_simp [hΔ]
      ring
    · dsimp [compose, inverseMetric, identityMetric, det]
      field_simp [hΔ]
      ring
    · dsimp [compose, inverseMetric, identityMetric, det]
      calc
        (-c / (a * d - b * c)) * b + (a / (a * d - b * c)) * d
            = (a * d - c * b) / (a * d - b * c) := by
              field_simp [hΔ]
              ring
        _ = (a * d - b * c) / (a * d - b * c) := by ring
        _ = 1 := by
              field_simp [hΔ]

/-- Linear Onsager flux in the `β` channel for force vector `(xβ, xμ)`. -/
def betaFlux (M : ResponseMatrix2) (xβ xμ : ℝ) : ℝ :=
  M.betaBeta * xβ + M.betaMu * xμ

/-- Linear Onsager flux in the `μ` channel for force vector `(xβ, xμ)`. -/
def muFlux (M : ResponseMatrix2) (xβ xμ : ℝ) : ℝ :=
  M.muBeta * xβ + M.muMu * xμ

/--
Entropy production for the finite two-channel Onsager response:
`σ = X · L X`.
-/
def entropyProduction (M : ResponseMatrix2) (xβ xμ : ℝ) : ℝ :=
  xβ * M.betaFlux xβ xμ + xμ * M.muFlux xβ xμ

/--
Strict positive-definite Onsager gate for the finite response packet.

This is intentionally stronger than `PositiveSemidefinite`: it says the
entropy-production quadratic form is strictly positive on every nonzero force
vector.  It is the finite hypothesis needed for the equality case
`σ = 0 ↔ X = 0`.
-/
def PositiveDefinite (M : ResponseMatrix2) : Prop :=
  ∀ xβ xμ : ℝ, (xβ ≠ 0 ∨ xμ ≠ 0) → 0 < M.entropyProduction xβ xμ

/-- Under Onsager symmetry, entropy production is the associated quadratic form. -/
lemma entropyProduction_eq_quadratic_of_symmetric
    {M : ResponseMatrix2} (hSym : M.Symmetric) (xβ xμ : ℝ) :
    M.entropyProduction xβ xμ =
      M.betaBeta * xβ ^ (2 : ℕ) +
        2 * M.betaMu * xβ * xμ +
          M.muMu * xμ ^ (2 : ℕ) := by
  dsimp [entropyProduction, betaFlux, muFlux, Symmetric] at hSym ⊢
  rw [← hSym]
  ring

/--
Finite Onsager second-law shadow: a symmetric positive-semidefinite response
matrix has nonnegative entropy production for every force vector.
-/
theorem entropyProduction_nonneg_of_symmetric_positiveSemidefinite
    {M : ResponseMatrix2}
    (hSym : M.Symmetric) (hPSD : M.PositiveSemidefinite)
    (xβ xμ : ℝ) :
  0 ≤ M.entropyProduction xβ xμ := by
  rcases hPSD with ⟨hββ, hμμ, hdet⟩
  have hdet0 : 0 ≤ M.betaBeta * M.muMu - M.betaMu * M.muBeta := by
    simpa [det] using hdet
  rw [← hSym] at hdet0
  have hdet' : 0 ≤ M.betaBeta * M.muMu - M.betaMu ^ (2 : ℕ) := by
    simpa [pow_two] using hdet0
  by_cases hββ_zero : M.betaBeta = 0
  · have hb_sq_nonpos : M.betaMu ^ (2 : ℕ) ≤ 0 := by
      nlinarith
    have hb_sq_zero : M.betaMu ^ (2 : ℕ) = 0 :=
      le_antisymm hb_sq_nonpos (sq_nonneg M.betaMu)
    have hb_zero : M.betaMu = 0 := by
      exact sq_eq_zero_iff.mp hb_sq_zero
    rw [entropyProduction_eq_quadratic_of_symmetric hSym, hββ_zero, hb_zero]
    nlinarith [sq_nonneg xμ, hμμ]
  · have hββ_pos : 0 < M.betaBeta := lt_of_le_of_ne hββ (Ne.symm hββ_zero)
    have hnum_nonneg :
        0 ≤ (M.betaBeta * xβ + M.betaMu * xμ) ^ (2 : ℕ) +
          (M.betaBeta * M.muMu - M.betaMu ^ (2 : ℕ)) *
            xμ ^ (2 : ℕ) :=
      add_nonneg (sq_nonneg _)
        (mul_nonneg hdet' (sq_nonneg xμ))
    have hquad :
        M.entropyProduction xβ xμ =
          ((M.betaBeta * xβ + M.betaMu * xμ) ^ (2 : ℕ) +
            (M.betaBeta * M.muMu - M.betaMu ^ (2 : ℕ)) *
              xμ ^ (2 : ℕ)) / M.betaBeta := by
      rw [entropyProduction_eq_quadratic_of_symmetric hSym]
      field_simp [hββ_zero]
      ring
    rw [hquad]
    exact div_nonneg hnum_nonneg hββ

/--
Strict finite Onsager equality case: under a positive-definite response gate,
zero entropy production is equivalent to zero thermodynamic force.
-/
theorem entropyProduction_eq_zero_iff_force_zero_of_positiveDefinite
    {M : ResponseMatrix2}
    (hPD : M.PositiveDefinite)
    (xβ xμ : ℝ) :
    M.entropyProduction xβ xμ = 0 ↔ xβ = 0 ∧ xμ = 0 := by
  constructor
  · intro hzero
    by_contra hforce
    have hnonzero : xβ ≠ 0 ∨ xμ ≠ 0 := by
      by_cases hβ : xβ = 0
      · right
        intro hμ
        exact hforce ⟨hβ, hμ⟩
      · exact Or.inl hβ
    have hpos : 0 < M.entropyProduction xβ xμ :=
      hPD xβ xμ hnonzero
    rw [hzero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  · rintro ⟨rfl, rfl⟩
    simp [entropyProduction, betaFlux, muFlux]

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

/-- The ββ response is the variance of the shifted observable `E - μN`. -/
theorem betaHessian_eq_varianceShift
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    betaHessian params β μ = varianceShift params β μ := by
  simpa [betaHessian, betaResponse, potentialBetaSlice] using
    potentialGC_hessian_beta_beta params β μ

/-- The concrete ββ response is nonnegative because it is a variance. -/
theorem betaHessian_nonneg
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    0 ≤ betaHessian params β μ := by
  rw [betaHessian_eq_varianceShift]
  exact varianceShift_nonneg params β μ

/-- The μμ response is `β²` times the variance of the number observable. -/
theorem muHessian_eq_beta_sq_varianceNumber
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    muHessian params β μ =
      β ^ (2 : ℕ) * varianceNumber params β μ := by
  simpa [muHessian, muResponse, potentialMuSlice] using
    potentialGC_hessian_mu_mu params β μ

/-- The concrete μμ response is nonnegative because it is `β²` times a variance. -/
theorem muHessian_nonneg
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    0 ≤ muHessian params β μ := by
  rw [muHessian_eq_beta_sq_varianceNumber]
  exact mul_nonneg (sq_nonneg β) (varianceNumber_nonneg params β μ)

/-- The `∂_μ ∂_β` response is the number mean minus `β` times cross covariance. -/
theorem betaMuHessian_eq_meanNumber_sub_beta_mul_covariance
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    betaMuHessian params β μ =
      meanNumber params β μ - β * covarianceShiftNumber params β μ := by
  simpa [betaMuHessian, betaResponse, potentialBetaSlice] using
    potentialGC_hessian_beta_mu params β μ

/-- The `∂_β ∂_μ` response is the same number/covariance readout. -/
theorem muBetaHessian_eq_meanNumber_sub_beta_mul_covariance
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    muBetaHessian params β μ =
      meanNumber params β μ - β * covarianceShiftNumber params β μ := by
  simpa [muBetaHessian, muResponse, potentialMuSlice] using
    potentialGC_hessian_mu_beta params β μ

/-- Concrete mixed-partial symmetry of the grand-canonical response matrix. -/
theorem betaMuHessian_eq_muBetaHessian
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    betaMuHessian params β μ = muBetaHessian params β μ := by
  rw [betaMuHessian_eq_meanNumber_sub_beta_mul_covariance,
    muBetaHessian_eq_meanNumber_sub_beta_mul_covariance]

/-- The concrete grand-canonical response matrix is symmetric. -/
theorem responseMatrix_symmetric_of_hessian
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    (responseMatrix params β μ).Symmetric :=
  betaMuHessian_eq_muBetaHessian params β μ

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

/--
Concrete PSD interface for the grand-canonical response matrix.

The diagonal entries are no longer hypotheses: they are proven variances.
Only the determinant/non-spinodal side condition remains explicit.
-/
theorem responseMatrix_positiveSemidefinite_of_det_nonneg
    (params : GrandCanonicalTwoParam α) (β μ : ℝ)
    (hdet : 0 ≤ (responseMatrix params β μ).det) :
    (responseMatrix params β μ).PositiveSemidefinite :=
  responseMatrix_positiveSemidefinite params β μ
    (betaHessian_nonneg params β μ)
    (muHessian_nonneg params β μ)
    hdet

omit [Nonempty α] in
/-- The two-parameter spinodal locus is exactly determinant degeneracy. -/
lemma spinodal2D_iff_det_eq_zero
    (params : GrandCanonicalTwoParam α) (β μ : ℝ) :
    Spinodal2D params β μ ↔ (responseMatrix params β μ).det = 0 :=
  Iff.rfl

end InfoGeometry.GrandCanonical
