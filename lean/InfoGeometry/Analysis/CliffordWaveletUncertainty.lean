import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Analysis.CliffordWaveletTransform

/-!
# InfoGeometry.Analysis.CliffordWaveletUncertainty

Clifford-wavelet uncertainty principle.

Literature owner:
  H. Banouh, A. Ben Mabrouk, M. Kesri,
  "Clifford-wavelet Transform and the uncertainty principle",
  arXiv:1905.10169.

This file owns the uncertainty-principle layer for Clifford wavelets.

It does not assert any prime-number, zeta, Mertens, Lee--Yang, or RH theorem.
-/

noncomputable section
set_option linter.dupNamespace false

namespace CliffordWaveletUncertainty

open InfoGeometry.Analysis.CliffordWaveletTransform

/-- Abstract uncertainty readout for a Clifford wavelet model. -/
@[rep_depth operator]
structure CliffordWaveletUncertainty
    (W : CliffordWaveletModel) where
  /-- Squared norm of a signal. -/
  normSq : W.Signal → ℝ

  /-- Spatial/logarithmic-scale variance. -/
  spaceVariance : W.Signal → ℝ

  /-- Spectral/wavelet-frequency variance. -/
  spectralVariance : W.Signal → ℝ

  /-- Positive uncertainty constant. -/
  uncertaintyConstant : ℝ

  uncertaintyConstant_pos :
    0 < uncertaintyConstant

  normSq_nonneg :
    ∀ f, 0 ≤ normSq f

  spaceVariance_nonneg :
    ∀ f, 0 ≤ spaceVariance f

  spectralVariance_nonneg :
    ∀ f, 0 ≤ spectralVariance f

  /-- Clifford-wavelet Heisenberg-type uncertainty inequality. -/
  heisenberg_clifford_wavelet :
    W.admissible →
      ∀ f : W.Signal,
        uncertaintyConstant * (normSq f)^2
          ≤ spaceVariance f * spectralVariance f

namespace CliffordWaveletUncertaintyOps

variable {W : CliffordWaveletModel}
variable (U : CliffordWaveletUncertainty W)

/-- Re-export of the Clifford-wavelet uncertainty inequality. -/
@[rep_depth operator]
theorem heisenberg
    (hAdm : W.admissible)
    (f : W.Signal) :
    U.uncertaintyConstant * (U.normSq f)^2
      ≤ U.spaceVariance f * U.spectralVariance f :=
  U.heisenberg_clifford_wavelet hAdm f

/-- Lemma 1: a nonzero squared norm gives a positive squared norm. -/
@[rep_depth operator]
theorem normSq_sq_pos_of_ne_zero
    (f : W.Signal)
    (hf : U.normSq f ≠ 0) :
    0 < (U.normSq f)^2 := by
  exact sq_pos_of_ne_zero hf

/-- Lemma 2: the uncertainty left-hand side is strictly positive for nonzero norm. -/
@[rep_depth operator]
theorem uncertainty_lhs_pos_of_normSq_ne_zero
    (f : W.Signal)
    (hf : U.normSq f ≠ 0) :
    0 < U.uncertaintyConstant * (U.normSq f)^2 := by
  exact mul_pos U.uncertaintyConstant_pos (normSq_sq_pos_of_ne_zero U f hf)

/-- Lemma 3: if both variances vanish, their product vanishes. -/
@[rep_depth operator]
theorem variance_product_eq_zero_of_both_zero
    (f : W.Signal)
    (hspace : U.spaceVariance f = 0)
    (hspec : U.spectralVariance f = 0) :
    U.spaceVariance f * U.spectralVariance f = 0 := by
  rw [hspace, hspec]
  ring

/-- Lemma 4: Heisenberg inequality forbids both variances to vanish for nonzero norm. -/
@[rep_depth operator]
theorem not_both_variances_zero_of_heisenberg
    (hAdm : W.admissible)
    (f : W.Signal)
    (hf : U.normSq f ≠ 0) :
    ¬ (U.spaceVariance f = 0 ∧ U.spectralVariance f = 0) := by
  intro hzero
  have hH := U.heisenberg_clifford_wavelet hAdm f
  have hpos := uncertainty_lhs_pos_of_normSq_ne_zero U f hf
  have hprod := variance_product_eq_zero_of_both_zero U f hzero.1 hzero.2
  rw [hprod] at hH
  nlinarith

/-- Theorem: an admissible nonzero-norm signal cannot have both variances zero. -/
@[rep_depth operator]
theorem noncollapse
    (hAdm : W.admissible)
    (f : W.Signal)
    (hf : U.normSq f ≠ 0) :
    U.spaceVariance f ≠ 0 ∨ U.spectralVariance f ≠ 0 := by
  by_contra h
  push_neg at h
  exact not_both_variances_zero_of_heisenberg U hAdm f hf ⟨h.1, h.2⟩

end CliffordWaveletUncertaintyOps

end CliffordWaveletUncertainty
