import InfoGeometry.Canonical.CanonicalZornFiveGradedClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealSplitOctZornCoreBridge

/-!
# Real split-octonion readback into the native five-graded projective closure

This owner transports `RealSplitOct` through the established coordinate
equivalence with `ZornCore.Zorn`, then reuses the native projective null-cone
and five-grade closure theorems.  It introduces no new carrier or product and
does not identify the associative Clifford algebra with Zorn multiplication.
-/

noncomputable section

namespace CanonicalZornFiveGradedClosure

open InfoGeometry.Algebra
open InfoGeometry.Canonical.RealSplitOctZornCoreBridge
open CanonicalZornProjectiveTKKBridge
open TKKJordanPairData.TKKGrade

def realSplitOctProjectiveVector (X : RealSplitOct) : ConformalIndex → ℝ :=
  zornProjectiveVector (realSplitOctToZornCore X)

theorem realSplitOctProjectiveVector_null (X : RealSplitOct) :
    conformalVectorQuadratic (realSplitOctProjectiveVector X) = 0 := by
  exact zornProjectiveVector_null (realSplitOctToZornCore X)

theorem realSplitOct_five_grade_projective_closure
    (X Y : RealSplitOct) :
    conformalVectorQuadratic (realSplitOctProjectiveVector X) = 0 ∧
    zornPositive (coreToCanonical (realSplitOctToZornCore X)) ∈
      conformalGrade p1 ∧
    zornNegative (coreToCanonical (realSplitOctToZornCore Y)) ∈
      conformalGrade m1 ∧
    ⁅zornNegative (coreToCanonical (realSplitOctToZornCore Y)),
        zornPositive (coreToCanonical (realSplitOctToZornCore X))⁆ ∈
      conformalGrade z0 ∧
    conformalTriality
        (zornPositive (coreToCanonical (realSplitOctToZornCore X))) =
      zornPositive
        (coreToCanonical
          (ZornCore.triality (realSplitOctToZornCore X))) := by
  simpa [realSplitOctProjectiveVector] using
    canonical_triality_five_grade_projective_closure
      (realSplitOctToZornCore X) (realSplitOctToZornCore Y)

end CanonicalZornFiveGradedClosure

end noncomputable section
