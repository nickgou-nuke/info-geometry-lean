import InfoGeometry.Canonical.FilteredGNSRepresentedCStarCompletion
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Readback for the completed C*-colimit carrier

The algebraic direct limit is only a star-algebra.  The C*-structure belongs
to the faithful represented completion, where the norm and completeness are
actually available.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

def representedAlgebraicRangeCompletion_cStarAlgebra :
    CStarAlgebra
      (representedAlgebraicRangeCompletion Stage sys ω) := by
  infer_instance

end CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion
