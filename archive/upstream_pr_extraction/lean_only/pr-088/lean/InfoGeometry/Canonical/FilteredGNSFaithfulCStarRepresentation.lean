import InfoGeometry.Canonical.FilteredGNSFaithfulAlgebraicQuotient
import InfoGeometry.Canonical.FilteredGNSRepresentedCStarClosure
import InfoGeometry.Canonical.AlgebraicStarEnvelopeNorm

/-!
# Faithful C-star realization of the algebraic GNS colimit

The represented algebraic range embeds into its concrete operator-norm
C-star closure.  This file packages that native star-algebra map as a
`FaithfulStarRepresentation`, but only under the explicit injectivity
hypothesis on the algebraic GNS range map.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSFaithfulCStarRepresentation

set_option maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSFaithfulAlgebraicQuotient
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure

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

lemma algebraicColimitToRepresentedClosure_eq_inclusion_range
    (a : AlgebraicStarDirectLimit Stage sys) :
    algebraicColimitToRepresentedClosure Stage sys ω a =
      representedAlgebraicRangeInclusion Stage sys ω
        (rangeStarAlgHom Stage sys ω a) := by
  apply Subtype.ext
  rfl

def faithfulStarRepresentation
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    FaithfulStarRepresentation
      (A := AlgebraicStarDirectLimit Stage sys)
      (B := representedCStarClosure Stage sys ω) where
  rep := (representedAlgebraicRangeInclusion Stage sys ω).comp
    (rangeStarAlgHom Stage sys ω)
  faithful := by
    intro a b hab
    have hrange : rangeAlgHom Stage sys ω a =
        rangeAlgHom Stage sys ω b := by
      change rangeStarAlgHom Stage sys ω a =
        rangeStarAlgHom Stage sys ω b
      exact representedAlgebraicRangeInclusion_injective
        Stage sys ω hab
    exact hρ hrange

@[simp] lemma faithfulStarRepresentation_apply
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    (faithfulStarRepresentation Stage sys ω hρ).rep a =
      representedAlgebraicRangeInclusion Stage sys ω
        (rangeStarAlgHom Stage sys ω a) := rfl

@[simp] lemma faithfulStarRepresentation_apply_eq_closureMap
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    (faithfulStarRepresentation Stage sys ω hρ).rep a =
      algebraicColimitToRepresentedClosure Stage sys ω a := by
  rw [faithfulStarRepresentation_apply]
  symm
  exact algebraicColimitToRepresentedClosure_eq_inclusion_range
    (Stage := Stage) (sys := sys) (ω := ω) a

/-- The faithful pullback norm induced by the represented C⋆-closure. -/
abbrev faithfulPulledNorm
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    AlgebraicStarDirectLimit Stage sys → ℝ :=
  (faithfulStarRepresentation Stage sys ω hρ).pulledNorm

/-- The faithful pullback ring norm induced by the represented C⋆-closure. -/
noncomputable abbrev faithfulPulledRingNorm
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    RingNorm (AlgebraicStarDirectLimit Stage sys) :=
  (faithfulStarRepresentation Stage sys ω hρ).pulledRingNorm

/-- The normed-ring structure transported from the represented C⋆-closure
under explicit faithfulness `hρ`. -/
noncomputable abbrev faithfulPulledNormedRing
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    NormedRing (AlgebraicStarDirectLimit Stage sys) :=
  (faithfulStarRepresentation Stage sys ω hρ).pulledNormedRing

theorem faithfulPulledNorm_eq_closureNorm
    (hρ : Function.Injective (rangeAlgHom Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    faithfulPulledNorm Stage sys ω hρ a =
      ‖algebraicColimitToRepresentedClosure Stage sys ω a‖ := by
  change ‖(faithfulStarRepresentation Stage sys ω hρ).rep a‖ =
    ‖algebraicColimitToRepresentedClosure Stage sys ω a‖
  rw [faithfulStarRepresentation_apply_eq_closureMap
    (Stage := Stage) (sys := sys) (ω := ω) hρ a]

theorem algebraicColimitToRepresentedClosure_isometry
    (hρ : Function.Injective (rangeAlgHom Stage sys ω)) :
    letI := faithfulPulledNormedRing Stage sys ω hρ
    Isometry (algebraicColimitToRepresentedClosure Stage sys ω) := by
  letI := faithfulPulledNormedRing Stage sys ω hρ
  have hIsoRep : Isometry ((faithfulStarRepresentation Stage sys ω hρ).rep) :=
    (faithfulStarRepresentation Stage sys ω hρ).rep_isometry
  simpa [faithfulStarRepresentation_apply_eq_closureMap
    (Stage := Stage) (sys := sys) (ω := ω) hρ] using hIsoRep

end CStarStateColimit.Native.FilteredGNSFaithfulCStarRepresentation
