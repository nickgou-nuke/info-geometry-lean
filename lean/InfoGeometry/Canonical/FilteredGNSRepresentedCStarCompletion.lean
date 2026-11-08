import InfoGeometry.Canonical.FilteredGNSRepresentedAlgebraCompletion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.StarAlgEquivPullback

/-!
# C-star algebra structure on the completed represented GNS range

The canonical linear isometric equivalence from the completion of the
faithful represented algebraic range to the represented operator closure
preserves multiplication and the unit.  It therefore upgrades to an algebra
equivalence.

The operator adjoint is then transported back across this equivalence.  The
resulting involution is continuous, agrees with the original involution on
the dense algebraic range, and satisfies the star-ring, complex star-module,
and C-star identities.  Consequently the completion is a native
`CStarAlgebra`, canonically star-algebra equivalent to the concrete
represented closure.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedRangeCompletion
open CStarStateColimit.Native.FilteredGNSRepresentedAlgebraCompletion

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

local instance gnsHilbertColimitCompleteSpace :
    CompleteSpace (GNSHilbertColimit Stage sys ω) :=
  gnsHilbertColimit_complete Stage sys ω

local instance globalBoundedOperatorCStarAlgebra :
    CStarAlgebra
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) where

local instance representedAlgebraicRangeAddCommGroup :
    AddCommGroup (representedAlgebraicRange Stage sys ω) := by
  change AddCommGroup
    {x : GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω //
      x ∈ (algebraicColimitGNSRepresentation Stage sys ω).range}
  infer_instance

instance representedAlgebraicRangeCompletionCompleteSpace :
    CompleteSpace (representedAlgebraicRangeCompletion Stage sys ω) :=
  UniformSpace.Completion.completeSpace
    (representedAlgebraicRange Stage sys ω)

instance representedAlgebraicRangeCompletionNormedAlgebra :
    NormedAlgebra ℂ (representedAlgebraicRangeCompletion Stage sys ω) where
  norm_smul_le := norm_smul_le

local instance representedAlgebraicRangeIsUniformAddGroup :
    IsUniformAddGroup (representedAlgebraicRange Stage sys ω) := by
  change IsUniformAddGroup
    {x : GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω //
      x ∈ (algebraicColimitGNSRepresentation Stage sys ω).range}
  infer_instance

local instance representedAlgebraicRangeModule :
    Module ℂ (representedAlgebraicRange Stage sys ω) :=
  Submodule.module
    ((representedAlgebraicRange Stage sys ω).toSubalgebra.toSubmodule)

local instance representedAlgebraicRangeNormedSpace :
    NormedSpace ℂ (representedAlgebraicRange Stage sys ω) :=
  (representedAlgebraicRange Stage sys ω).toSubalgebra.toSubmodule.normedSpace

local instance representedAlgebraicRangeUniformContinuousConstSMul :
    UniformContinuousConstSMul ℂ (representedAlgebraicRange Stage sys ω) := by
  change UniformContinuousConstSMul ℂ
    {x : GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω //
      x ∈ (algebraicColimitGNSRepresentation Stage sys ω).range}
  infer_instance

instance representedAlgebraicRangeCompletionStarRing :
    StarRing (representedAlgebraicRangeCompletion Stage sys ω) := by
  let e := representedRangeCompletionAlgEquiv Stage sys ω
  exact
    { star := fun x => e.symm (star (e x))
      star_involutive := by
        intro x
        apply e.injective
        simp
      star_add := by
        intro x y
        apply e.injective
        simp
      star_mul := by
        intro x y
        apply e.injective
        simp }

@[simp] theorem representedRangeCompletionAlgEquiv_map_star
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionAlgEquiv Stage sys ω (star x) =
      star (representedRangeCompletionAlgEquiv Stage sys ω x) := by
  exact StarAlgEquivPullback.starRing_map_star
    (representedRangeCompletionAlgEquiv Stage sys ω) x

instance representedAlgebraicRangeCompletionStarModule :
    StarModule ℂ
      (representedAlgebraicRangeCompletion Stage sys ω) where
  star_smul c x := by
    apply (representedRangeCompletionAlgEquiv Stage sys ω).injective
    calc
      representedRangeCompletionAlgEquiv Stage sys ω
          (star (c • x)) =
        star
          (representedRangeCompletionAlgEquiv Stage sys ω
            (c • x)) :=
        representedRangeCompletionAlgEquiv_map_star Stage sys ω _
      _ = star
          (c • representedRangeCompletionAlgEquiv Stage sys ω x) := by
        rw [map_smul]
      _ = star c •
          star (representedRangeCompletionAlgEquiv Stage sys ω x) :=
        star_smul _ _
      _ = star c •
          representedRangeCompletionAlgEquiv Stage sys ω (star x) := by
        exact congrArg (star c • ·)
          (representedRangeCompletionAlgEquiv_map_star
            Stage sys ω x).symm
      _ = representedRangeCompletionAlgEquiv Stage sys ω
          (star c • star x) := by
        exact
          (map_smul
            (representedRangeCompletionAlgEquiv
              Stage sys ω) (star c) (star x)).symm

/-- The transported involution is continuous in the operator-norm completion
topology. -/
instance representedAlgebraicRangeCompletionContinuousStar :
    ContinuousStar
      (representedAlgebraicRangeCompletion Stage sys ω) where
  continuous_star := by
    change Continuous
      (fun x =>
        (representedRangeCompletionAlgEquiv Stage sys ω).symm
          (star (representedRangeCompletionAlgEquiv Stage sys ω x)))
    exact
      (representedRangeCompletionEquiv
        Stage sys ω).symm.continuous.comp
        (continuous_star.comp
          (representedRangeCompletionEquiv
            Stage sys ω).continuous)

/-- The transported involution agrees exactly with the original operator
involution on the dense represented algebraic range. -/
@[simp] theorem representedAlgebraicRangeCompletion_coe_star
    (x : representedAlgebraicRange Stage sys ω) :
    star
        (x :
          representedAlgebraicRangeCompletion Stage sys ω) =
      ((star x : representedAlgebraicRange Stage sys ω) :
        representedAlgebraicRangeCompletion Stage sys ω) := by
  apply (representedRangeCompletionAlgEquiv Stage sys ω).injective
  calc
    representedRangeCompletionAlgEquiv Stage sys ω
        (star
          (x :
            representedAlgebraicRangeCompletion Stage sys ω)) =
      star
        (representedRangeCompletionAlgEquiv Stage sys ω
          (x :
            representedAlgebraicRangeCompletion Stage sys ω)) :=
      representedRangeCompletionAlgEquiv_map_star Stage sys ω _
    _ = star (representedAlgebraicRangeInclusion Stage sys ω x) := by
      rw [representedRangeCompletionAlgEquiv_coe]
    _ = representedAlgebraicRangeInclusion Stage sys ω (star x) :=
      (representedAlgebraicRangeInclusion_star Stage sys ω x).symm
    _ = representedRangeCompletionAlgEquiv Stage sys ω
        ((star x : representedAlgebraicRange Stage sys ω) :
          representedAlgebraicRangeCompletion Stage sys ω) := by
      rw [representedRangeCompletionAlgEquiv_coe]

instance representedAlgebraicRangeCompletionCStarRing :
    CStarRing
      (representedAlgebraicRangeCompletion Stage sys ω) where
  norm_mul_self_le :=
    StarAlgEquivPullback.norm_mul_self_le
      (representedRangeCompletionAlgEquiv Stage sys ω)
      (representedRangeCompletionToClosure_norm Stage sys ω)

/-- The completed faithful range is a native C-star algebra. -/
instance representedAlgebraicRangeCompletionCStarAlgebra :
    CStarAlgebra
      (representedAlgebraicRangeCompletion Stage sys ω) where
  toNormedRing := inferInstance
  toStarRing := representedAlgebraicRangeCompletionStarRing Stage sys ω
  toCompleteSpace :=
    representedAlgebraicRangeCompletionCompleteSpace Stage sys ω
  toCStarRing := representedAlgebraicRangeCompletionCStarRing Stage sys ω
  toNormedAlgebra := inferInstance
  toStarModule := representedAlgebraicRangeCompletionStarModule Stage sys ω

/-- Canonical star-algebra equivalence between the completed faithful
represented range and the concrete represented C-star closure. -/
def representedRangeCompletionStarAlgEquiv :
    representedAlgebraicRangeCompletion Stage sys ω ≃⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω where
  toFun := representedRangeCompletionAlgEquiv Stage sys ω
  invFun := (representedRangeCompletionAlgEquiv Stage sys ω).symm
  left_inv :=
    (representedRangeCompletionAlgEquiv Stage sys ω).left_inv
  right_inv :=
    (representedRangeCompletionAlgEquiv Stage sys ω).right_inv
  map_add' :=
    (representedRangeCompletionAlgEquiv Stage sys ω).map_add
  map_mul' :=
    (representedRangeCompletionAlgEquiv Stage sys ω).map_mul
  map_smul' := fun c x =>
    map_smul
      (representedRangeCompletionAlgEquiv Stage sys ω) c x
  map_star' :=
    representedRangeCompletionAlgEquiv_map_star Stage sys ω

@[simp] theorem representedRangeCompletionStarAlgEquiv_apply
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionStarAlgEquiv Stage sys ω x =
      representedRangeCompletionEquiv Stage sys ω x :=
  rfl

end CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion
