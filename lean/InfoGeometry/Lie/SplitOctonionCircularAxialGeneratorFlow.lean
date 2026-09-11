import InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading

/-!
# The axial grading as a linear flow generator

This owner treats the circular axial grading as a linear endomorphism of the
split-octonion carrier.  It does not treat it as a derivation or as an
automorphism of the nonassociative multiplication.  The flow is the diagonal
linear flow already defined in the axial-grading owner, and its generator is
identified by a genuine `HasDerivAt` statement.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularAxialGeneratorFlow

open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev CanonicalZorn :=
  InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.CanonicalZorn

theorem hasDerivAt_axialFlow_coordinate (X : CanonicalZorn) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordinateEquiv (axialFlow s X))
      (coordinateEquiv (axialGrading (axialFlow t X))) t := by
  let hcoord : HasDerivAt
      (fun s : ℝ => coordinateEquiv (axialFlow s X))
      (coordinateEquiv (axialGrading (axialFlow t X))) t := by
    rw [hasDerivAt_pi]
    intro i
    simp only [coordinateEquiv_axialFlow_apply,
      coordinateEquiv_axialGrading_apply]
    have harg : HasDerivAt
        (fun s : ℝ => s * axialWeight i)
        (1 * axialWeight i) t :=
      (hasDerivAt_id t).mul_const (axialWeight i)
    have hexp : HasDerivAt
        (fun s : ℝ => Real.exp (s * axialWeight i))
        (Real.exp (t * axialWeight i) * (1 * axialWeight i)) t :=
      by
        simpa only [Function.comp_apply] using
          (Real.hasDerivAt_exp (t * axialWeight i)).comp t harg
    convert hexp.mul_const (coordinateEquiv X i) using 1 <;> ring
  exact hcoord

theorem axialFlow_initial (X : CanonicalZorn) :
    axialFlow 0 X = X :=
  axialFlow_zero_apply X

theorem axialFlow_group (s t : ℝ) (X : CanonicalZorn) :
    axialFlow (s + t) X = axialFlow s (axialFlow t X) :=
  axialFlow_add_apply s t X

theorem axialFlow_inverse (t : ℝ) (X : CanonicalZorn) :
    axialFlow (-t) (axialFlow t X) = X := by
  calc
    axialFlow (-t) (axialFlow t X) = axialFlow (-t + t) X := by
      symm
      exact axialFlow_group (-t) t X
    _ = X := by rw [neg_add_cancel, axialFlow_zero_apply]

/-!
The generator is a linear grading operator, not a derivation of the
split-octonion multiplication.  This is an intentional nonassociative
boundary, not an omitted instance.
-/
theorem axialGrading_not_derivation_boundary :
    ¬ IsDerivation axialGrading :=
  circularAxialGrading_not_derivation

end InfoGeometry.Lie.SplitOctonionCircularAxialGeneratorFlow
