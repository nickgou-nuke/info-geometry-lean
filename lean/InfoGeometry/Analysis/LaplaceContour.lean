import InfoGeometry.Analysis.LaplaceUniqueness

/-!
# InfoGeometry.Analysis.LaplaceContour

Vertical-line contour packaging for the Laplace transform.

This module makes the contour hypotheses explicit:
* holomorphy on a strip;
* decay on the horizontal arcs;
* a residue law.

The current inversion theorem is still reduction-based, via the existing
Bromwich/Fourier inversion package.  The contour hypotheses are exposed as
first-class data so that a future native contour proof can plug in without
changing the interface.
-/

noncomputable section

namespace InfoGeometry.Analysis.LaplaceContour

open scoped FourierTransform RealInnerProductSpace
open Set MeasureTheory

/-!
## Contour hypotheses
-/

/-- Holomorphic strip data for a Bromwich contour package. -/
structure StripHolomorphic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  σ : ℝ
  f : ℝ → E
  holomorphicOnStrip : Prop

/-- Horizontal decay data for a Bromwich contour package. -/
structure HorizontalDecay (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  σ : ℝ
  f : ℝ → E
  upperArcDecay : Prop
  lowerArcDecay : Prop

/-- Vertical-line contour admissibility data for Laplace inversion. -/
structure ContourAdmissible (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  strip : StripHolomorphic E
  decay : HorizontalDecay E
  residueLaw : Prop

namespace ContourAdmissible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/--
Bromwich contour readout packaged from the vertical-line transform.

The contour hypotheses are carried explicitly by `ContourAdmissible`; the
current readout still uses the native vertical-line transform package.
-/
def BromwichContourIntegral (A : ContourAdmissible E) : ℝ → E :=
  InfoGeometry.Analysis.LaplaceUniqueness.bromwichVerticalLineTransform
    (E := E) A.strip.σ A.strip.f

/-- The Bromwich contour readout is the vertical-line transform of the package. -/
theorem BromwichContourIntegral_eq_verticalLineTransform
    (A : ContourAdmissible E) :
    BromwichContourIntegral (E := E) A =
      InfoGeometry.Analysis.LaplaceUniqueness.bromwichVerticalLineTransform
        (E := E) A.strip.σ A.strip.f := rfl

/--
Bromwich inversion law packaged with residue and arc-decay hypotheses.

This theorem is still proved by the existing Bromwich/Fourier inversion route;
the contour hypotheses are explicit data for a future native contour proof.
-/
theorem BromwichInversionLaw
    (A : ContourAdmissible E)
    (hf : MeasureTheory.Integrable (fun t : ℝ =>
      Complex.exp (-(A.strip.σ * (t : ℂ))) • A.strip.f t))
    (h'f : MeasureTheory.Integrable
      (FourierTransform.fourier (fun t : ℝ =>
        Complex.exp (-(A.strip.σ * (t : ℂ))) • A.strip.f t)))
    (hcf : Continuous A.strip.f) :
    (fun t : ℝ =>
      Complex.exp ((A.strip.σ * (t : ℂ))) •
        FourierTransformInv.fourierInv (BromwichContourIntegral (E := E) A) t) =
      A.strip.f := by
  simpa [BromwichContourIntegral] using
    (InfoGeometry.Analysis.LaplaceUniqueness.bromwich_inversion_on_vertical_line
      (f := A.strip.f) (σ := A.strip.σ) hf h'f hcf)

end ContourAdmissible

end InfoGeometry.Analysis.LaplaceContour
