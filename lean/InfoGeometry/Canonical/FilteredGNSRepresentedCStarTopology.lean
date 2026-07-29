import InfoGeometry.Canonical.FilteredGNSRepresentedCStarCompletion

/-!
# Topological API for the completed represented C-star equivalence

The represented completion is already identified with the concrete operator
closure by a complex linear isometry.  This owner exposes the corresponding
homeomorphism and its continuity laws, rather than reproving topological facts
from norms or coordinates.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarTopology

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

/-- The canonical homeomorphism underlying the completed represented
`StarAlgEquiv`. -/
def representedRangeCompletionHomeomorph :
    representedAlgebraicRangeCompletion Stage sys ω ≃ₜ
      representedCStarClosure Stage sys ω :=
  (representedRangeCompletionEquiv Stage sys ω).toHomeomorph

@[simp] theorem representedRangeCompletionHomeomorph_apply
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionHomeomorph Stage sys ω x =
      representedRangeCompletionStarAlgEquiv Stage sys ω x :=
  rfl

theorem representedRangeCompletionHomeomorph_continuous :
    Continuous (representedRangeCompletionHomeomorph Stage sys ω) :=
  (representedRangeCompletionEquiv Stage sys ω).continuous

theorem representedRangeCompletionHomeomorph_continuous_inv :
    Continuous (representedRangeCompletionHomeomorph Stage sys ω).symm :=
  (representedRangeCompletionEquiv Stage sys ω).symm.continuous

theorem representedRangeCompletionStarAlgEquiv_continuous :
    Continuous (representedRangeCompletionStarAlgEquiv Stage sys ω) := by
  simpa [representedRangeCompletionStarAlgEquiv] using
    (representedRangeCompletionEquiv Stage sys ω).continuous

theorem representedRangeCompletionStarAlgEquiv_continuous_inv :
    Continuous (representedRangeCompletionStarAlgEquiv Stage sys ω).symm := by
  simpa [representedRangeCompletionStarAlgEquiv] using
    (representedRangeCompletionEquiv Stage sys ω).symm.continuous

end CStarStateColimit.Native.FilteredGNSRepresentedCStarTopology
