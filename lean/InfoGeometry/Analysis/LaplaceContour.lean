import InfoGeometry.Analysis.LaplaceUniqueness

/-! 
# InfoGeometry.Analysis.LaplaceContour

Vertical-line contour packaging for the Laplace transform.

This module makes the contour hypotheses explicit:
* holomorphy on a strip;
* decay on the horizontal arcs;

The current inversion theorem is still reduction-based, via the existing
Bromwich/Fourier inversion package.  A native residue-theorem contour proof is
not supplied here.
-/

noncomputable section

namespace InfoGeometry.Analysis.LaplaceContour

open scoped FourierTransform RealInnerProductSpace
open Set MeasureTheory
open Filter

/-!
## Contour hypotheses
-/

/-- Open vertical strip between real parts `sigma_lo` and `sigma_hi`. -/
def verticalStrip (sigma_lo sigma_hi : ℝ) : Set ℂ :=
  {z : ℂ | sigma_lo < z.re ∧ z.re < sigma_hi}

/-- Holomorphic strip data for a Bromwich contour package. -/
structure StripHolomorphic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  abscissa : ℝ
  f : ℝ → E
  /-- Complex transform continued to a vertical strip. -/
  transform : ℂ → E
  strip_lo : ℝ
  strip_hi : ℝ
  contour_mem_strip : strip_lo < abscissa ∧ abscissa < strip_hi
  /-- Genuine Mathlib holomorphy on the open strip. -/
  holomorphicOnStrip :
    DifferentiableOn ℂ transform (verticalStrip strip_lo strip_hi)

/-- Horizontal decay data for a Bromwich contour package. -/
structure HorizontalDecay (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  abscissa : ℝ
  f : ℝ → E
  /--
  Truncated upper and lower horizontal contour contributions.  Concrete
  contour models define these by interval integrals along their horizontal
  paths.
  -/
  upperArcIntegral : ℝ → E
  lowerArcIntegral : ℝ → E
  /-- The upper horizontal contribution vanishes as the truncation grows. -/
  upperArcDecay :
    Tendsto upperArcIntegral atTop (nhds 0)
  /-- The lower horizontal contribution vanishes as the truncation grows. -/
  lowerArcDecay :
    Tendsto lowerArcIntegral atTop (nhds 0)

/-- Vertical-line contour admissibility data for Laplace inversion. -/
structure ContourAdmissible (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  strip : StripHolomorphic E
  decay : HorizontalDecay E
  decay_sigma_eq : decay.abscissa = strip.abscissa
  decay_source_eq : decay.f = strip.f

namespace ContourAdmissible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/--
Bromwich contour readout packaged from the vertical-line transform.

The contour hypotheses are carried explicitly by `ContourAdmissible`; the
current readout still uses the native vertical-line transform package.
-/
def BromwichContourIntegral (A : ContourAdmissible E) : ℝ → E :=
  InfoGeometry.Analysis.LaplaceUniqueness.bromwichVerticalLineTransform
    (E := E) A.strip.abscissa A.strip.f

/-- The Bromwich contour readout is the vertical-line transform of the package. -/
theorem BromwichContourIntegral_eq_verticalLineTransform
    (A : ContourAdmissible E) :
    BromwichContourIntegral (E := E) A =
      InfoGeometry.Analysis.LaplaceUniqueness.bromwichVerticalLineTransform
        (E := E) A.strip.abscissa A.strip.f := rfl

/--
Bromwich inversion law packaged with strip and arc-decay data.

This theorem is still proved by the existing Bromwich/Fourier inversion route;
no residue theorem is proved in this file.
-/
theorem BromwichInversionLaw
    [CompleteSpace E]
    (A : ContourAdmissible E)
    (hf : MeasureTheory.Integrable (fun t : ℝ =>
      Complex.exp (-(A.strip.abscissa * (t : ℂ))) • A.strip.f t))
    (h'f : MeasureTheory.Integrable
      (FourierTransform.fourier (fun t : ℝ =>
        Complex.exp (-(A.strip.abscissa * (t : ℂ))) • A.strip.f t)))
    (hcf : Continuous A.strip.f) :
    (fun t : ℝ =>
      Complex.exp ((A.strip.abscissa * (t : ℂ))) •
        FourierTransformInv.fourierInv (BromwichContourIntegral (E := E) A) t) =
      A.strip.f := by
  simpa [BromwichContourIntegral] using
    (InfoGeometry.Analysis.LaplaceUniqueness.bromwich_inversion_on_vertical_line
      (f := A.strip.f) (σ := A.strip.abscissa) hf h'f hcf)

end ContourAdmissible

end InfoGeometry.Analysis.LaplaceContour
