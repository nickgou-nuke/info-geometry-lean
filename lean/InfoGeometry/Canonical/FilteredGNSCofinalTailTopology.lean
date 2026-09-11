import InfoGeometry.Canonical.FilteredGNSCofinalTail
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Topological API for cofinal GNS tail equivalences

The cofinal-tail construction produces a surjective linear isometry by dense
stage transport.  This owner exposes its native topological realization as a
homeomorphism, with continuity of both directions inherited from
`LinearIsometryEquiv`.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSCofinalTailTopology

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSCofinalTail
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSTailStarRepresentation
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricInnerProductDirectLimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

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

/-- The canonical homeomorphism from a cofinal-tail Hilbert colimit to the
global filtered GNS Hilbert colimit. -/
def tailHilbertGlobalHomeomorph (i₀ : I) :
    HilbertDirectLimit (TailGNSStage Stage sys ω i₀)
        (tailGNSIsometricDirectSystem Stage sys ω i₀) ≃ₜ
      GNSHilbertColimit Stage sys ω :=
  (tailHilbertGlobalEquiv Stage sys ω i₀).toHomeomorph

@[simp] theorem tailHilbertGlobalHomeomorph_apply
    (i₀ : I)
    (x : HilbertDirectLimit (TailGNSStage Stage sys ω i₀)
      (tailGNSIsometricDirectSystem Stage sys ω i₀)) :
    tailHilbertGlobalHomeomorph Stage sys ω i₀ x =
      tailHilbertGlobalEquiv Stage sys ω i₀ x :=
  rfl

theorem tailHilbertGlobalHomeomorph_continuous (i₀ : I) :
    Continuous (tailHilbertGlobalHomeomorph Stage sys ω i₀) :=
  (tailHilbertGlobalEquiv Stage sys ω i₀).continuous

theorem tailHilbertGlobalHomeomorph_continuous_inv (i₀ : I) :
    Continuous (tailHilbertGlobalHomeomorph Stage sys ω i₀).symm :=
  (tailHilbertGlobalEquiv Stage sys ω i₀).symm.continuous

@[simp] theorem tailHilbertGlobalHomeomorph_stage
    (i₀ : I) (j : UpperIndex i₀) (x : TailGNSStage Stage sys ω i₀ j) :
    tailHilbertGlobalHomeomorph Stage sys ω i₀
        (stageToHilbertDirectLimit
          (TailGNSStage Stage sys ω i₀)
          (tailGNSIsometricDirectSystem Stage sys ω i₀) j x) =
      gnsStageToHilbertColimit Stage sys ω j.1 x :=
  tailHilbertGlobalEquiv_stage Stage sys ω i₀ j x

end CStarStateColimit.Native.FilteredGNSCofinalTailTopology
