import InfoGeometry.Canonical.FilteredGNSFaithfulRangeQuotient
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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

universe v

/-- A norm-preserving linear map, bundled as a linear isometry. -/
def normPreservingLinearMapToIsometry
    {A B : Type v}
    [SeminormedAddCommGroup A] [Module ℂ A]
    [SeminormedAddCommGroup B] [Module ℂ B]
    (f : A →ₗ[ℂ] B) (h : ∀ x, ‖f x‖ = ‖x‖) : A →ₗᵢ[ℂ] B :=
  LinearIsometry.mk f h

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000
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

instance gnsHilbertColimitCompleteSpace :
    CompleteSpace (GNSHilbertColimit Stage sys ω) :=
  gnsHilbertColimit_complete Stage sys ω

local instance representedCStarClosureCompleteSpace :
    CompleteSpace (representedCStarClosure Stage sys ω) :=
  (StarSubalgebra.isClosed_topologicalClosure _).completeSpace_coe

/-- Uniform operator-norm completion of the faithful represented algebraic
range. -/
abbrev representedAlgebraicRangeCompletion :=
  UniformSpace.Completion
    (representedAlgebraicRange Stage sys ω)

instance representedAlgebraicRangeAddCommGroup :
    AddCommGroup (representedAlgebraicRange Stage sys ω) := by
  change AddCommGroup
    {x : GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω //
      x ∈ (algebraicColimitGNSRepresentation Stage sys ω).range}
  infer_instance

instance representedAlgebraicRangeIsUniformAddGroup :
    IsUniformAddGroup (representedAlgebraicRange Stage sys ω) := by
  change IsUniformAddGroup
    {x : GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω //
      x ∈ (algebraicColimitGNSRepresentation Stage sys ω).range}
  infer_instance

instance representedAlgebraicRangeModule :
    Module ℂ (representedAlgebraicRange Stage sys ω) :=
  Submodule.module
    ((representedAlgebraicRange Stage sys ω).toSubalgebra.toSubmodule)

instance representedAlgebraicRangeNormedSpace :
    NormedSpace ℂ (representedAlgebraicRange Stage sys ω) :=
  (representedAlgebraicRange Stage sys ω).toSubalgebra.toSubmodule.normedSpace

/-- Mathlib provides the represented range's `SeminormedRing` structure via
its native subring instance.  Select its corresponding non-unital structure
directly: the generic search also tries the `NonUnitalNormedRing` route, which
does not apply to this dense, generally incomplete subalgebra. -/
instance representedAlgebraicRangeNonUnitalSeminormedRing :
    NonUnitalSeminormedRing (representedAlgebraicRange Stage sys ω) :=
  @SeminormedRing.toNonUnitalSeminormedRing _
    (inferInstance : SeminormedRing (representedAlgebraicRange Stage sys ω))

instance representedAlgebraicRangeUniformContinuousConstSMul :
    UniformContinuousConstSMul ℂ (representedAlgebraicRange Stage sys ω) := by
  change UniformContinuousConstSMul ℂ
    {x : GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω //
      x ∈ (algebraicColimitGNSRepresentation Stage sys ω).range}
  infer_instance

/-- The faithful range inclusion as a complex linear map, obtained directly
from the native star-algebra inclusion. -/
def representedAlgebraicRangeLinearMap :
    representedAlgebraicRange Stage sys ω →ₗ[ℂ]
      representedCStarClosure Stage sys ω where
  toFun := representedAlgebraicRangeInclusion Stage sys ω
  map_add' := by
    intro x y
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c x
    apply Subtype.ext
    rfl

/-- The faithful range inclusion, bundled as a complex linear isometry. -/
def representedAlgebraicRangeLinearIsometry :
    representedAlgebraicRange Stage sys ω →ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
  normPreservingLinearMapToIsometry
    (representedAlgebraicRangeLinearMap Stage sys ω)
    (fun _ => rfl)

@[simp] theorem representedAlgebraicRangeLinearIsometry_apply
    (x : representedAlgebraicRange Stage sys ω) :
    representedAlgebraicRangeLinearIsometry Stage sys ω x =
      representedAlgebraicRangeInclusion Stage sys ω x := rfl

/-- Continuous extension of the faithful range inclusion to its uniform
completion using Mathlib's dense uniform embedding extension. -/
def representedRangeCompletionToClosureCLM :
    representedAlgebraicRangeCompletion Stage sys ω →L[ℂ]
      representedCStarClosure Stage sys ω :=
  let f : representedAlgebraicRange Stage sys ω →ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
    representedAlgebraicRangeLinearIsometry Stage sys ω
  ContinuousLinearMap.fromCompletion f.toContinuousLinearMap

@[simp] theorem representedRangeCompletionToClosureCLM_coe
    (x : representedAlgebraicRange Stage sys ω) :
    representedRangeCompletionToClosureCLM Stage sys ω x =
      representedAlgebraicRangeInclusion Stage sys ω x := by
  let f : representedAlgebraicRange Stage sys ω →ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
    representedAlgebraicRangeLinearIsometry Stage sys ω
  change f.fromCompletion x = _
  exact LinearIsometry.fromCompletion_apply_coe f x

/-- The completion extension preserves the operator norm exactly. -/
theorem representedRangeCompletionToClosure_norm
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    ‖representedRangeCompletionToClosureCLM Stage sys ω x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      change IsClosed
        {y : representedAlgebraicRangeCompletion Stage sys ω |
          ‖representedRangeCompletionToClosureCLM Stage sys ω y‖ = ‖y‖}
      have hleft : Continuous
          (fun y : representedAlgebraicRangeCompletion Stage sys ω =>
            ‖representedRangeCompletionToClosureCLM Stage sys ω y‖) :=
        continuous_norm.comp
          (representedRangeCompletionToClosureCLM Stage sys ω).continuous
      have hright : Continuous
          (fun y : representedAlgebraicRangeCompletion Stage sys ω => ‖y‖) :=
        @continuous_norm
          (representedAlgebraicRangeCompletion Stage sys ω)
          (inferInstance : SeminormedAddGroup
            (representedAlgebraicRangeCompletion Stage sys ω))
      exact isClosed_eq hleft hright
  | ih x =>
      simpa only [representedRangeCompletionToClosureCLM_coe,
        representedAlgebraicRangeLinearIsometry_apply,
        UniformSpace.Completion.norm_coe] using
          (representedAlgebraicRangeLinearIsometry Stage sys ω).norm_map x

/-- The completion map bundled as a complex linear isometry. -/
def representedRangeCompletionToClosureLinearIsometry :
    representedAlgebraicRangeCompletion Stage sys ω →ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
  LinearIsometry.mk
    (representedRangeCompletionToClosureCLM Stage sys ω).toLinearMap
    (representedRangeCompletionToClosure_norm Stage sys ω)

theorem representedRangeCompletionToClosureLinearIsometry_norm
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    ‖representedRangeCompletionToClosureLinearIsometry Stage sys ω x‖ = ‖x‖ :=
  (representedRangeCompletionToClosureLinearIsometry Stage sys ω).norm_map x

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
  let e : representedAlgebraicRangeCompletion Stage sys ω →ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
    representedRangeCompletionToClosureLinearIsometry Stage sys ω
  have hIso : Isometry e := e.isometry
  have hanti : AntilipschitzWith 1 e := hIso.antilipschitzWith
  have huc : UniformContinuous e :=
    hIso.lipschitzWith.uniformContinuous
  have hclosed : IsClosed (Set.range e) := hanti.isClosed_range huc
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
      representedCStarClosure Stage sys ω := by
  let f : representedAlgebraicRangeCompletion Stage sys ω →ₗᵢ[ℂ]
      representedCStarClosure Stage sys ω :=
    representedRangeCompletionToClosureLinearIsometry Stage sys ω
  exact LinearIsometryEquiv.ofSurjective
    (F := representedAlgebraicRangeCompletion Stage sys ω)
    (E₂ := representedCStarClosure Stage sys ω)
    (σ₁₂ := RingHom.id ℂ) f
    (representedRangeCompletionToClosure_surjective Stage sys ω)

@[simp] theorem representedRangeCompletionEquiv_coe
    (x : representedAlgebraicRange Stage sys ω) :
    representedRangeCompletionEquiv Stage sys ω x =
      representedAlgebraicRangeInclusion Stage sys ω x :=
  by
    change representedRangeCompletionToClosureLinearIsometry
      Stage sys ω x = _
    exact representedRangeCompletionToClosureCLM_coe Stage sys ω x

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
