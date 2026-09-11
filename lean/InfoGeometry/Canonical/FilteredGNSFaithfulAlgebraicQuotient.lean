import InfoGeometry.Canonical.FilteredGNSFaithfulRangeQuotient
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Star.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Faithful quotient of the algebraic GNS colimit

The global GNS representation may have a non-trivial kernel on the raw
algebraic colimit.  The honest faithful carrier is therefore the ideal
quotient by that kernel.  Mathlib's first-isomorphism theorem identifies this
quotient with the represented algebraic range.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSFaithfulAlgebraicQuotient

set_option maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSOperatorSeminormKernel
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
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

def rangeAlgHom :
    AlgebraicStarDirectLimit Stage sys →ₐ[ℂ]
      representedAlgebraicRange Stage sys ω :=
  (algebraicColimitRangeRestrict Stage sys ω).toAlgHom

def rangeStarAlgHom :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      representedAlgebraicRange Stage sys ω :=
  algebraicColimitRangeRestrict Stage sys ω

/-! Faithfulness is exactly kernel-triviality; no GNS faithfulness is assumed. -/

abbrev Kernel := RingHom.ker (rangeAlgHom Stage sys ω).toRingHom

abbrev KernelQuotient :=
  AlgebraicStarDirectLimit Stage sys ⧸
    Kernel Stage sys ω

theorem rangeAlgHom_surjective :
    Function.Surjective (rangeAlgHom Stage sys ω) := by
  exact algebraicColimitRangeRestrict_surjective Stage sys ω

/-! ### Faithfulness criterion -/

theorem rangeAlgHom_injective_iff_ker_eq_bot :
    Function.Injective (rangeAlgHom Stage sys ω) ↔
      Kernel Stage sys ω = ⊥ := by
  exact RingHom.injective_iff_ker_eq_bot
    (rangeAlgHom Stage sys ω).toRingHom

theorem rangeAlgHom_injective_of_ker_eq_bot
    (hker : Kernel Stage sys ω = ⊥) :
    Function.Injective (rangeAlgHom Stage sys ω) := by
  exact rangeAlgHom_injective_iff_ker_eq_bot Stage sys ω |>.2 hker

theorem kernel_eq_bot_of_injective
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    RingHom.ker (rangeAlgHom Stage sys ω).toRingHom = ⊥ := by
  exact (RingHom.injective_iff_ker_eq_bot
    (rangeAlgHom Stage sys ω).toRingHom).1 hρ

/-- The quotient by the GNS kernel is canonically the represented range.

This is the noncommutative first-isomorphism theorem: the result is a
`RingEquiv`, not an `AlgEquiv`, because Mathlib's range theorem for arbitrary
noncommutative rings does not assume commutativity of the coefficient action.
-/
noncomputable def quotientRangeRingEquiv :
    KernelQuotient Stage sys ω ≃+*
      representedAlgebraicRange Stage sys ω := by
  exact RingHom.quotientKerEquivOfSurjective
    (rangeAlgHom_surjective Stage sys ω)

@[simp] theorem quotientRangeRingEquiv_mk
    (a : AlgebraicStarDirectLimit Stage sys) :
    quotientRangeRingEquiv Stage sys ω
        (Ideal.Quotient.mk _ a) =
      algebraicColimitRangeRestrict Stage sys ω a := by
  rfl

theorem quotientRangeRingEquiv_injective :
    Function.Injective (quotientRangeRingEquiv Stage sys ω) :=
  (quotientRangeRingEquiv Stage sys ω).injective

theorem quotientRangeRingEquiv_surjective :
    Function.Surjective (quotientRangeRingEquiv Stage sys ω) :=
  (quotientRangeRingEquiv Stage sys ω).surjective

/-- Under a genuine faithfulness hypothesis, the raw colimit itself is
identified with the represented range; the quotient presentation is then
unnecessary. -/
noncomputable def rawToRangeRingEquiv
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    AlgebraicStarDirectLimit Stage sys ≃+*
      representedAlgebraicRange Stage sys ω :=
  RingEquiv.ofBijective
    (rangeAlgHom Stage sys ω).toRingHom
    ⟨hρ, rangeAlgHom_surjective Stage sys ω⟩

@[simp] theorem rawToRangeRingEquiv_apply
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    rawToRangeRingEquiv Stage sys ω hρ a =
      rangeAlgHom Stage sys ω a :=
  rfl

/-- Under the same genuine faithfulness hypothesis, the represented map is
upgraded from a ring equivalence to the native star-algebra equivalence. -/
noncomputable def rawToRangeStarAlgEquiv
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    AlgebraicStarDirectLimit Stage sys ≃⋆ₐ[ℂ]
      representedAlgebraicRange Stage sys ω :=
  StarAlgEquiv.ofBijective
    (rangeStarAlgHom Stage sys ω)
    ⟨hρ, rangeAlgHom_surjective Stage sys ω⟩

@[simp] theorem rawToRangeStarAlgEquiv_apply
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    rawToRangeStarAlgEquiv Stage sys ω hρ a =
      rangeStarAlgHom Stage sys ω a :=
  rfl

end CStarStateColimit.Native.FilteredGNSFaithfulAlgebraicQuotient
