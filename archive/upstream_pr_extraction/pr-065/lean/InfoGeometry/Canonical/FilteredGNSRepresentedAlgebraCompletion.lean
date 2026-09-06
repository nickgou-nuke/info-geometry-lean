import InfoGeometry.Canonical.FilteredGNSRepresentedRangeCompletion

/-!
# Algebra structure on the completed represented GNS range

Mathlib's native `Isometry.extensionHom` extends the faithful represented
range inclusion to a ring homomorphism on its uniform completion.  This
completed ring homomorphism agrees with the canonical linear isometric
equivalence to the represented operator closure.  Hence that equivalence
preserves the unit and noncommutative multiplication and upgrades to an
`AlgEquiv`.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedAlgebraCompletion

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

/-- Native Mathlib extension of the faithful represented-range ring
homomorphism to the uniform completion. -/
def representedRangeCompletionRingHom :
    representedAlgebraicRangeCompletion Stage sys ω →+*
      representedCStarClosure Stage sys ω := by
  have h :
      Isometry
        (representedAlgebraicRangeInclusion Stage sys ω :
          representedAlgebraicRange Stage sys ω →
            representedCStarClosure Stage sys ω) :=
    (representedAlgebraicRangeLinearIsometry
      Stage sys ω).isometry
  exact h.extensionHom

@[simp] theorem representedRangeCompletionRingHom_coe
    (x : representedAlgebraicRange Stage sys ω) :
    representedRangeCompletionRingHom Stage sys ω
        (x :
          representedAlgebraicRangeCompletion Stage sys ω) =
      representedAlgebraicRangeInclusion Stage sys ω x := by
  unfold representedRangeCompletionRingHom
  apply Isometry.extensionHom_coe

/-- The native completed ring homomorphism is exactly the previously
constructed completion isometry. -/
theorem representedRangeCompletionRingHom_eq_equiv
    (x : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionRingHom Stage sys ω x =
      representedRangeCompletionEquiv Stage sys ω x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((representedAlgebraicRangeLinearIsometry
        Stage sys ω).isometry.completion_extension.continuous)
      (representedRangeCompletionEquiv Stage sys ω).continuous
  | ih x =>
    rw [representedRangeCompletionRingHom_coe,
      representedRangeCompletionEquiv_coe]

/-- The completion equivalence preserves noncommutative multiplication by
Mathlib's native isometric ring-homomorphism extension. -/
theorem representedRangeCompletionEquiv_map_mul
    (x y : representedAlgebraicRangeCompletion Stage sys ω) :
    representedRangeCompletionEquiv Stage sys ω (x * y) =
      representedRangeCompletionEquiv Stage sys ω x *
        representedRangeCompletionEquiv Stage sys ω y := by
  calc
    representedRangeCompletionEquiv Stage sys ω (x * y) =
        representedRangeCompletionRingHom Stage sys ω (x * y) :=
      (representedRangeCompletionRingHom_eq_equiv
        Stage sys ω (x * y)).symm
    _ = representedRangeCompletionRingHom Stage sys ω x *
        representedRangeCompletionRingHom Stage sys ω y :=
      map_mul (representedRangeCompletionRingHom Stage sys ω) x y
    _ = representedRangeCompletionEquiv Stage sys ω x *
        representedRangeCompletionEquiv Stage sys ω y := by
      exact congrArg₂ (· * ·)
        (representedRangeCompletionRingHom_eq_equiv
          Stage sys ω x)
        (representedRangeCompletionRingHom_eq_equiv
          Stage sys ω y)

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

@[simp] theorem representedRangeCompletionAlgEquiv_coe
    (x : representedAlgebraicRange Stage sys ω) :
    representedRangeCompletionAlgEquiv Stage sys ω
        (x :
          representedAlgebraicRangeCompletion Stage sys ω) =
      representedAlgebraicRangeInclusion Stage sys ω x := by
  rw [representedRangeCompletionAlgEquiv_apply,
    representedRangeCompletionEquiv_coe]

end CStarStateColimit.Native.FilteredGNSRepresentedAlgebraCompletion
