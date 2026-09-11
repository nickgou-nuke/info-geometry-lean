import InfoGeometry.Canonical.FilteredGNSRepresentedCStarCompletion
import InfoGeometry.Algebra.FiniteSpinAlgebra

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
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedAlgebraCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation

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

/-- The algebraic and topological equivalences combine into Mathlib's native
continuous algebra equivalence. -/
def representedRangeCompletionContinuousAlgEquiv :
    representedAlgebraicRangeCompletion Stage sys ω ≃A[ℂ]
      representedCStarClosure Stage sys ω :=
  ContinuousAlgEquiv.mk
    (representedRangeCompletionAlgEquiv Stage sys ω)
    (representedRangeCompletionEquiv Stage sys ω).continuous
    (representedRangeCompletionEquiv Stage sys ω).symm.continuous

@[simp] theorem representedRangeCompletionContinuousAlgEquiv_apply
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionContinuousAlgEquiv Stage sys ω x =
      representedRangeCompletionStarAlgEquiv Stage sys ω x := by
  change representedRangeCompletionAlgEquiv Stage sys ω x =
    representedRangeCompletionAlgEquiv Stage sys ω x
  rfl

@[simp] theorem representedRangeCompletionContinuousAlgEquiv_symm_apply
    (x : representedCStarClosure Stage sys ω) :
    (representedRangeCompletionContinuousAlgEquiv Stage sys ω).symm x =
      (representedRangeCompletionStarAlgEquiv Stage sys ω).symm x := by
  change (representedRangeCompletionAlgEquiv Stage sys ω).symm x =
    (representedRangeCompletionAlgEquiv Stage sys ω).symm x
  rfl

/- The continuous equivalence preserves the verified finite-stage cocone
formula on the canonical dense completion inclusion. -/
@[simp] theorem representedRangeCompletionContinuousAlgEquiv_stage
    (i : I) (a : Stage i) :
    representedRangeCompletionContinuousAlgEquiv Stage sys ω
        (algebraicColimitRangeRestrict Stage sys ω
          (algebraicStarDirectLimitOf Stage sys i a)) =
      algebraicColimitToRepresentedClosure Stage sys ω
        (algebraicStarDirectLimitOf Stage sys i a) := by
  change representedRangeCompletionEquiv Stage sys ω
      (algebraicColimitRangeRestrict Stage sys ω
        (algebraicStarDirectLimitOf Stage sys i a)) =
    algebraicColimitToRepresentedClosure Stage sys ω
      (algebraicStarDirectLimitOf Stage sys i a)
  exact representedRangeCompletionEquiv_stage Stage sys ω i a

/- The continuous algebra equivalence transports the canonical dense
completion inclusion to a dense subset of the represented C-star closure.
This is a topological consequence of the uniform completion API and the
surjectivity of the bundled equivalence; no finite enumeration is involved. -/
theorem representedRangeCompletionContinuousAlgEquiv_coe_denseRange :
    DenseRange
      (fun x : representedAlgebraicRange Stage sys ω =>
        representedRangeCompletionContinuousAlgEquiv Stage sys ω
          (x : representedAlgebraicRangeCompletion Stage sys ω)) := by
  have h_equiv :
      DenseRange
        (representedRangeCompletionContinuousAlgEquiv Stage sys ω) :=
    (representedRangeCompletionContinuousAlgEquiv Stage sys ω).surjective.denseRange
  have h_coe :
      DenseRange
        (fun x : representedAlgebraicRange Stage sys ω =>
          (x : representedAlgebraicRangeCompletion Stage sys ω)) :=
    UniformSpace.Completion.denseRange_coe
  simpa [Function.comp_def] using
    h_equiv.comp h_coe
      (representedRangeCompletionHomeomorph_continuous
        Stage sys ω)

end CStarStateColimit.Native.FilteredGNSRepresentedCStarTopology
