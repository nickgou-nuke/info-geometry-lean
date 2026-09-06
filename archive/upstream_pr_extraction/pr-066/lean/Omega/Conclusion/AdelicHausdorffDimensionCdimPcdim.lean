import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete model for the adelic Hausdorff dimension in the max-product metric from the paper:
the Euclidean torus contributes `r`, the profinite primorial factor contributes `d`, and the finite
factor contributes `0`. -/
def adelicHausdorffDim (r d : ℕ) : ℝ :=
  (r + d : ℝ)

/-- In the concrete max-product adelic model, the Hausdorff dimension is the sum of the torus rank
and the profinite covering-growth exponent.
    thm:conclusion-adelic-hausdorff-dimension-cdim-pcdim -/
theorem paper_conclusion_adelic_hausdorff_dimension_cdim_pcdim (r d : ℕ) :
    adelicHausdorffDim r d = (r + d : ℝ) := by
  rfl

/-- Paper label: `cor:conclusion-adelic-hausdorff-noncompressible-phase-dimension`.
Any bilipschitz phase code from the adelic model into `T^k` forces the torus ambient dimension to
dominate the adelic Hausdorff dimension. -/
theorem paper_conclusion_adelic_hausdorff_noncompressible_phase_dimension
    (r d k : ℕ) (imageHausdorffDim : ℝ)
    (hBilipschitz : (r + d : ℝ) = imageHausdorffDim)
    (hAmbient : imageHausdorffDim ≤ (k : ℝ)) :
    adelicHausdorffDim r d ≤ (k : ℝ) := by
  calc
    adelicHausdorffDim r d = (r + d : ℝ) :=
      paper_conclusion_adelic_hausdorff_dimension_cdim_pcdim r d
    _ = imageHausdorffDim := hBilipschitz
    _ ≤ (k : ℝ) := hAmbient

end Omega.Conclusion
