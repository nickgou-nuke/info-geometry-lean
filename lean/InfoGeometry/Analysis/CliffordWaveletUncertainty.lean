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

namespace InfoGeometry.Analysis.CliffordWaveletUncertainty

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

  /-- Non-collapse / localization tradeoff in the Clifford wavelet phase space. -/
  noncollapse_law : Prop

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

end CliffordWaveletUncertaintyOps

end InfoGeometry.Analysis.CliffordWaveletUncertainty
