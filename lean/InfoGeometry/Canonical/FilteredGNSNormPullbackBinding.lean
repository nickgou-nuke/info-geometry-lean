import InfoGeometry.Canonical.FilteredGNSFaithfulCStarRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# GNS norm pullback binding via faithful range equivalence

This owner binds the faithful algebraic-range equivalence
`rawToRangeStarAlgEquiv` into the generic `FaithfulStarRepresentation`
interface, so the pulled norm / transported topology from
`AlgebraicStarEnvelopeNorm` can be used directly on the raw algebraic colimit
under the explicit injectivity hypothesis `hρ`.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSNormPullbackBinding

set_option maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSFaithfulAlgebraicQuotient
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSFaithfulCStarRepresentation

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

/-- Raw algebraic colimit map into the represented C-star closure, written via
`rawToRangeStarAlgEquiv` followed by the native range inclusion. -/
def rawToRepresentedClosureStarAlgHom
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω :=
  (representedAlgebraicRangeInclusion Stage sys ω).comp
    (rawToRangeStarAlgEquiv Stage sys ω hρ)

@[simp] theorem rawToRepresentedClosureStarAlgHom_apply
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    rawToRepresentedClosureStarAlgHom Stage sys ω hρ a =
      representedAlgebraicRangeInclusion Stage sys ω
        (rangeStarAlgHom Stage sys ω a) := by
  simp [rawToRepresentedClosureStarAlgHom, rawToRangeStarAlgEquiv_apply]

/-- The explicit GNS faithfulness hypothesis upgrades the raw algebraic colimit
into a concrete faithful C-star representation, suitable for norm pullback. -/
def faithfulStarRepresentationFromRawEquiv
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    FaithfulStarRepresentation
      (A := AlgebraicStarDirectLimit Stage sys)
      (B := representedCStarClosure Stage sys ω) where
  rep := rawToRepresentedClosureStarAlgHom Stage sys ω hρ
  faithful := by
    intro a b hab
    have hab' :
        representedAlgebraicRangeInclusion Stage sys ω
            (rangeStarAlgHom Stage sys ω a) =
          representedAlgebraicRangeInclusion Stage sys ω
            (rangeStarAlgHom Stage sys ω b) := by
      simpa [rawToRepresentedClosureStarAlgHom, rawToRangeStarAlgEquiv_apply] using hab
    have hrange : rangeStarAlgHom Stage sys ω a =
        rangeStarAlgHom Stage sys ω b := by
      exact representedAlgebraicRangeInclusion_injective
        Stage sys ω hab'
    exact hρ (by simpa [rangeAlgHom, rangeStarAlgHom] using hrange)

@[simp] theorem faithfulStarRepresentationFromRawEquiv_apply
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    (faithfulStarRepresentationFromRawEquiv Stage sys ω hρ).rep a =
      representedAlgebraicRangeInclusion Stage sys ω
        (rangeStarAlgHom Stage sys ω a) :=
  rawToRepresentedClosureStarAlgHom_apply Stage sys ω hρ a


/-- Pulled norm on the raw algebraic colimit obtained from the represented
closure through `rawToRangeStarAlgEquiv`. -/
def pulledNormFromRawEquiv
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) : ℝ :=
  (faithfulStarRepresentationFromRawEquiv Stage sys ω hρ).pulledNorm a

@[simp] theorem pulledNormFromRawEquiv_star
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    pulledNormFromRawEquiv Stage sys ω hρ (star a) =
      pulledNormFromRawEquiv Stage sys ω hρ a := by
  exact FaithfulStarRepresentation.pulledNorm_star
    (faithfulStarRepresentationFromRawEquiv Stage sys ω hρ) a

theorem pulledNormFromRawEquiv_star_mul_self
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    pulledNormFromRawEquiv Stage sys ω hρ (star a * a) =
      pulledNormFromRawEquiv Stage sys ω hρ a *
        pulledNormFromRawEquiv Stage sys ω hρ a := by
  simpa [pulledNormFromRawEquiv,
    FaithfulStarRepresentation.pulledRingNorm_apply] using
    FaithfulStarRepresentation.pulledRingNorm_star_mul_self
      (faithfulStarRepresentationFromRawEquiv Stage sys ω hρ) a

end CStarStateColimit.Native.FilteredGNSNormPullbackBinding
