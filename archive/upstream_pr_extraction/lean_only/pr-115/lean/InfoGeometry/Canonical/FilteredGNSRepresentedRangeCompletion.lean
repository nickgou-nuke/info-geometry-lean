import InfoGeometry.Canonical.FilteredGNSFaithfulRangeQuotient
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completion of the faithful represented GNS range

The concrete represented operator range carries the norm inherited from the
bounded endomorphism algebra.  Its canonical inclusion into the represented
C-star closure is a complex linear isometry with dense range.  Extending this
map from the uniform completion of the range gives a surjective linear
isometry, hence a canonical linear isometric equivalence with the represented
C-star closure.

This is an operator-norm completion theorem.  It does not identify the raw
algebraic star-colimit with a normed algebra before quotienting by the
representation kernel.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient

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

local instance globalBoundedOperatorCStarAlgebra :
    CStarAlgebra
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) where

/-- Uniform operator-norm completion of the faithful represented algebraic
range. -/
abbrev representedAlgebraicRangeCompletion :=
  UniformSpace.Completion
    (representedAlgebraicRange Stage sys ω)

/-- The faithful range inclusion, bundled as a complex linear isometry. -/
def representedAlgebraicRangeLinearIsometry :
    representedAlgebraicRange Stage sys ω →ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
  LinearIsometry.mk
    (representedAlgebraicRangeInclusion
      Stage sys ω).toAlgHom.toLinearMap
    (fun _ => rfl)

@[simp] theorem representedAlgebraicRangeLinearIsometry_apply
    (x : representedAlgebraicRange Stage sys ω) :
    representedAlgebraicRangeLinearIsometry Stage sys ω x =
      representedAlgebraicRangeInclusion Stage sys ω x :=
  rfl

/-- Continuous extension of the faithful range inclusion to its uniform
completion. -/
def representedRangeCompletionToClosureCLM :
    representedAlgebraicRangeCompletion Stage sys ω →L[ℂ]
      representedCStarClosure Stage sys ω :=
  (representedAlgebraicRangeLinearIsometry
    Stage sys ω).toContinuousLinearMap.extend
      (UniformSpace.Completion.toComplL :
        representedAlgebraicRange Stage sys ω →L[ℂ]
          representedAlgebraicRangeCompletion Stage sys ω)

@[simp] theorem representedRangeCompletionToClosureCLM_coe
    (x : representedAlgebraicRange Stage sys ω) :
    representedRangeCompletionToClosureCLM Stage sys ω x =
      representedAlgebraicRangeInclusion Stage sys ω x := by
  change
    ((representedAlgebraicRangeLinearIsometry
      Stage sys ω).toContinuousLinearMap.extend
        (UniformSpace.Completion.toComplL :
          representedAlgebraicRange Stage sys ω →L[ℂ]
            representedAlgebraicRangeCompletion Stage sys ω))
      ((UniformSpace.Completion.toComplL :
          representedAlgebraicRange Stage sys ω →L[ℂ]
            representedAlgebraicRangeCompletion Stage sys ω) x) =
        representedAlgebraicRangeInclusion Stage sys ω x
  exact ContinuousLinearMap.extend_eq
    (representedAlgebraicRangeLinearIsometry
      Stage sys ω).toContinuousLinearMap
    (e :=
      (UniformSpace.Completion.toComplL :
        representedAlgebraicRange Stage sys ω →L[ℂ]
          representedAlgebraicRangeCompletion Stage sys ω))
    UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _)
    x

/-- The completion extension preserves the operator norm exactly. -/
theorem representedRangeCompletionToClosure_norm
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    ‖representedRangeCompletionToClosureCLM Stage sys ω x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (continuous_norm.comp
        (representedRangeCompletionToClosureCLM
          Stage sys ω).continuous)
      continuous_norm
  | ih y =>
    rw [representedRangeCompletionToClosureCLM_coe,
      UniformSpace.Completion.norm_coe]
    rfl

/-- The completion map bundled as a complex linear isometry. -/
def representedRangeCompletionToClosureLinearIsometry :
    representedAlgebraicRangeCompletion Stage sys ω →ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
  LinearIsometry.mk
    (representedRangeCompletionToClosureCLM Stage sys ω)
    (representedRangeCompletionToClosure_norm Stage sys ω)

/-- The completed isometry has dense range because it contains the dense
algebraic represented range. -/
theorem representedRangeCompletionToClosure_denseRange :
    DenseRange
      (representedRangeCompletionToClosureLinearIsometry
        Stage sys ω) := by
  apply
    (representedAlgebraicRangeInclusion_denseRange
      Stage sys ω).mono
  intro y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨(x :
    representedAlgebraicRangeCompletion Stage sys ω), ?_⟩
  exact representedRangeCompletionToClosureCLM_coe
    Stage sys ω x

/-- The completed range is all of the represented C-star closure: the range
of an isometry from a complete space is closed, and it is dense by
construction. -/
theorem representedRangeCompletionToClosure_surjective :
    Function.Surjective
      (representedRangeCompletionToClosureLinearIsometry
        Stage sys ω) := by
  have hclosed :
      IsClosed
        (Set.range
          (representedRangeCompletionToClosureLinearIsometry
            Stage sys ω)) :=
    (representedRangeCompletionToClosureLinearIsometry
      Stage sys ω).isometry.isClosedEmbedding.isClosed_range
  have hdense :
      Dense
        (Set.range
          (representedRangeCompletionToClosureLinearIsometry
            Stage sys ω)) :=
    representedRangeCompletionToClosure_denseRange Stage sys ω
  intro y
  exact hdense.induction (fun x hx => hx) hclosed y

/-- Canonical complex linear isometric equivalence from the completion of the
faithful represented range onto the represented C-star closure. -/
def representedRangeCompletionEquiv :
    representedAlgebraicRangeCompletion Stage sys ω ≃ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
  LinearIsometryEquiv.ofSurjective
    (representedRangeCompletionToClosureLinearIsometry
      Stage sys ω)
    (representedRangeCompletionToClosure_surjective
      Stage sys ω)

@[simp] theorem representedRangeCompletionEquiv_coe
    (x : representedAlgebraicRange Stage sys ω) :
    representedRangeCompletionEquiv Stage sys ω x =
      representedAlgebraicRangeInclusion Stage sys ω x :=
  representedRangeCompletionToClosureCLM_coe Stage sys ω x

/-- On every finite-stage observable, the completion equivalence agrees
exactly with the verified global-stage representation inside the represented
C-star closure. -/
@[simp] theorem representedRangeCompletionEquiv_stage
    (i : I) (a : Stage i) :
    representedRangeCompletionEquiv Stage sys ω
        (algebraicColimitRangeRestrict Stage sys ω
          (algebraicStarDirectLimitOf Stage sys i a) :
          representedAlgebraicRangeCompletion Stage sys ω) =
      algebraicColimitToRepresentedClosure Stage sys ω
        (algebraicStarDirectLimitOf Stage sys i a) := by
  rw [representedRangeCompletionEquiv_coe]
  apply Subtype.ext
  rfl

/-- The dense faithful inclusion preserves the noncommutative involution
before completion. -/
@[simp] theorem representedAlgebraicRangeInclusion_star
    (x : representedAlgebraicRange Stage sys ω) :
    representedAlgebraicRangeInclusion Stage sys ω (star x) =
      star (representedAlgebraicRangeInclusion Stage sys ω x) :=
  map_star _ x

end CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion
