import InfoGeometry.Canonical.FilteredGNSRepresentedRangeCompletion

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

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
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
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

local instance globalBoundedOperatorCStarAlgebra :
    CStarAlgebra
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) where

/-- The completion equivalence preserves the multiplicative unit. -/
theorem representedRangeCompletionEquiv_map_one :
    representedRangeCompletionEquiv Stage sys ω
        (1 :
          representedAlgebraicRangeCompletion Stage sys ω) =
      1 := by
  rw [← UniformSpace.Completion.coe_one,
    representedRangeCompletionEquiv_coe]
  exact map_one
    (representedAlgebraicRangeInclusion Stage sys ω)

/-- The completion equivalence preserves noncommutative multiplication.
The proof descends from the dense represented algebraic range. -/
theorem representedRangeCompletionEquiv_map_mul
    (x y : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionEquiv Stage sys ω (x * y) =
      representedRangeCompletionEquiv Stage sys ω x *
        representedRangeCompletionEquiv Stage sys ω y := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    rw [← UniformSpace.Completion.coe_mul,
      representedRangeCompletionEquiv_coe,
      representedRangeCompletionEquiv_coe,
      representedRangeCompletionEquiv_coe]
    exact map_mul
      (representedAlgebraicRangeInclusion Stage sys ω) x y

/-- Canonical complex algebra equivalence between the completed faithful
range and the represented operator closure. -/
def representedRangeCompletionAlgEquiv :
    representedAlgebraicRangeCompletion Stage sys ω ≃ₐ[ℂ]
      representedCStarClosure Stage sys ω :=
  AlgEquiv.ofLinearEquiv
    (representedRangeCompletionEquiv
      Stage sys ω).toLinearEquiv
    (representedRangeCompletionEquiv_map_one Stage sys ω)
    (representedRangeCompletionEquiv_map_mul Stage sys ω)

@[simp] theorem representedRangeCompletionAlgEquiv_apply
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionAlgEquiv Stage sys ω x =
      representedRangeCompletionEquiv Stage sys ω x :=
  rfl

/-- Canonical involution on the completed faithful range, transported from
the operator adjoint on the represented C-star closure. -/
instance representedAlgebraicRangeCompletionStar :
    Star (representedAlgebraicRangeCompletion Stage sys ω) where
  star x :=
    (representedRangeCompletionAlgEquiv Stage sys ω).symm
      (star (representedRangeCompletionAlgEquiv Stage sys ω x))

@[simp] theorem representedRangeCompletionAlgEquiv_map_star
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionAlgEquiv Stage sys ω (star x) =
      star (representedRangeCompletionAlgEquiv Stage sys ω x) := by
  simp only [star, AlgEquiv.apply_symm_apply]

instance representedAlgebraicRangeCompletionInvolutiveStar :
    InvolutiveStar
      (representedAlgebraicRangeCompletion Stage sys ω) where
  star_involutive x := by
    apply (representedRangeCompletionAlgEquiv Stage sys ω).injective
    simp

instance representedAlgebraicRangeCompletionStarAddMonoid :
    StarAddMonoid
      (representedAlgebraicRangeCompletion Stage sys ω) where
  star_add x y := by
    apply (representedRangeCompletionAlgEquiv Stage sys ω).injective
    simp

instance representedAlgebraicRangeCompletionStarMul :
    StarMul
      (representedAlgebraicRangeCompletion Stage sys ω) where
  star_mul x y := by
    apply (representedRangeCompletionAlgEquiv Stage sys ω).injective
    simp

instance representedAlgebraicRangeCompletionStarModule :
    StarModule ℂ
      (representedAlgebraicRangeCompletion Stage sys ω) where
  star_smul c x := by
    apply (representedRangeCompletionAlgEquiv Stage sys ω).injective
    simp

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
  rw [representedRangeCompletionAlgEquiv_map_star]
  change
    star (representedAlgebraicRangeInclusion Stage sys ω x) =
      representedAlgebraicRangeInclusion Stage sys ω (star x)
  exact
    (representedAlgebraicRangeInclusion_star
      Stage sys ω x).symm

instance representedAlgebraicRangeCompletionCStarRing :
    CStarRing
      (representedAlgebraicRangeCompletion Stage sys ω) where
  norm_mul_self_le x := by
    have h :=
      CStarRing.norm_mul_self_le
        (representedRangeCompletionAlgEquiv Stage sys ω x)
    rw [← representedRangeCompletionAlgEquiv_map_star,
      ← map_mul,
      (representedRangeCompletionEquiv
        Stage sys ω).norm_map,
      (representedRangeCompletionEquiv
        Stage sys ω).norm_map] at h
    exact h

/-- The completed faithful range is a native C-star algebra. -/
instance representedAlgebraicRangeCompletionCStarAlgebra :
    CStarAlgebra
      (representedAlgebraicRangeCompletion Stage sys ω) where

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
  map_smul' :=
    (representedRangeCompletionAlgEquiv Stage sys ω).map_smul
  map_star' :=
    representedRangeCompletionAlgEquiv_map_star Stage sys ω

@[simp] theorem representedRangeCompletionStarAlgEquiv_apply
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionStarAlgEquiv Stage sys ω x =
      representedRangeCompletionEquiv Stage sys ω x :=
  rfl

end CStarStateColimit.Native.FilteredGNSRepresentedCStarCompletion
