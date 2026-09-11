import InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2RootAutRotationBridge
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/-!
# Structural second short-root / PC-word alignment

The concrete automorphism carrier is not equipped with a multiplication
instance in the native API. The canonical conjugation and PC alignment are
therefore read through the existing matrix/injective owner.
-/

namespace InfoGeometry.Algebra.Zorn.G2RootAutShortTwoStructural

open InfoGeometry.Algebra.Zorn.G2RootAutRotationBridge
open InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/-- The canonical corrected exponent for the second short root. -/
def shortTwoPCExp : PCWordExp := oneAt 5

/-- The existing native second short-root alignment, exposed at this owner. -/
theorem rootAut_short_two_eq_pcWord_structural :
    rootAut (RootLength.Short, (2 : ZMod 6)) =
      pcWord shortTwoPCExp := by
  exact rootAut_short_two_eq_correctedPCWord

end InfoGeometry.Algebra.Zorn.G2RootAutShortTwoStructural
