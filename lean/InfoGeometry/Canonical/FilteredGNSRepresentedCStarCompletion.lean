import InfoGeometry.Canonical.FilteredGNSRepresentedAlgebraCompletion

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

local instance globalBoundedOperatorCStarAlgebra :
    CStarAlgebra
      (GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) where

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
    calc
      representedRangeCompletionAlgEquiv Stage sys ω
          (star (star x)) =
        star
          (representedRangeCompletionAlgEquiv Stage sys ω
            (star x)) :=
        representedRangeCompletionAlgEquiv_map_star Stage sys ω _
      _ = star
          (star
            (representedRangeCompletionAlgEquiv Stage sys ω x)) := by
        rw [representedRangeCompletionAlgEquiv_map_star]
      _ = representedRangeCompletionAlgEquiv Stage sys ω x :=
        star_star _

instance representedAlgebraicRangeCompletionStarRing :
    StarRing
      (representedAlgebraicRangeCompletion Stage sys ω) where
  star_add x y := by
    apply (representedRangeCompletionAlgEquiv Stage sys ω).injective
    calc
      representedRangeCompletionAlgEquiv Stage sys ω
          (star (x + y)) =
        star
          (representedRangeCompletionAlgEquiv Stage sys ω
            (x + y)) :=
        representedRangeCompletionAlgEquiv_map_star Stage sys ω _
      _ = star
          (representedRangeCompletionAlgEquiv Stage sys ω x +
            representedRangeCompletionAlgEquiv Stage sys ω y) := by
        rw [map_add]
      _ = star (representedRangeCompletionAlgEquiv Stage sys ω x) +
          star (representedRangeCompletionAlgEquiv Stage sys ω y) :=
        star_add _ _
      _ = representedRangeCompletionAlgEquiv Stage sys ω (star x) +
          representedRangeCompletionAlgEquiv Stage sys ω (star y) := by
        exact congrArg₂ (· + ·)
          (representedRangeCompletionAlgEquiv_map_star
            Stage sys ω x).symm
          (representedRangeCompletionAlgEquiv_map_star
            Stage sys ω y).symm
      _ = representedRangeCompletionAlgEquiv Stage sys ω
          (star x + star y) := by
        exact
          ((representedRangeCompletionAlgEquiv
            Stage sys ω).map_add _ _).symm
  star_mul x y := by
    apply (representedRangeCompletionAlgEquiv Stage sys ω).injective
    calc
      representedRangeCompletionAlgEquiv Stage sys ω
          (star (x * y)) =
        star
          (representedRangeCompletionAlgEquiv Stage sys ω
            (x * y)) :=
        representedRangeCompletionAlgEquiv_map_star Stage sys ω _
      _ = star
          (representedRangeCompletionAlgEquiv Stage sys ω x *
            representedRangeCompletionAlgEquiv Stage sys ω y) := by
        rw [map_mul]
      _ = star (representedRangeCompletionAlgEquiv Stage sys ω y) *
          star (representedRangeCompletionAlgEquiv Stage sys ω x) :=
        star_mul _ _
      _ = representedRangeCompletionAlgEquiv Stage sys ω (star y) *
          representedRangeCompletionAlgEquiv Stage sys ω (star x) := by
        exact congrArg₂ (· * ·)
          (representedRangeCompletionAlgEquiv_map_star
            Stage sys ω y).symm
          (representedRangeCompletionAlgEquiv_map_star
            Stage sys ω x).symm
      _ = representedRangeCompletionAlgEquiv Stage sys ω
          (star y * star x) := by
        exact
          ((representedRangeCompletionAlgEquiv
            Stage sys ω).map_mul _ _).symm

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
  norm_mul_self_le x := by
    let e :=
      representedRangeCompletionAlgEquiv Stage sys ω
    have hnorm (z :
        representedAlgebraicRangeCompletion Stage sys ω) :
        ‖e z‖ = ‖z‖ :=
      (representedRangeCompletionEquiv
        Stage sys ω).norm_map z
    have hmap :
        e (star x * x) = star (e x) * e x := by
      calc
        e (star x * x) = e (star x) * e x :=
          e.map_mul _ _
        _ = star (e x) * e x := by
          rw [representedRangeCompletionAlgEquiv_map_star]
    calc
      ‖x‖ * ‖x‖ = ‖e x‖ * ‖e x‖ := by
        rw [hnorm]
      _ ≤ ‖star (e x) * e x‖ :=
        CStarRing.norm_mul_self_le (e x)
      _ = ‖e (star x * x)‖ := by
        rw [hmap]
      _ = ‖star x * x‖ :=
        hnorm _

/-- The completed faithful range is a native C-star algebra. -/
instance representedAlgebraicRangeCompletionCStarAlgebra :
    CStarAlgebra
      (representedAlgebraicRangeCompletion Stage sys ω) where
  norm_smul_le := norm_smul_le

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
