import InfoGeometry.Canonical.FilteredStarAlgebraDirectLimit
import InfoGeometry.Canonical.FilteredGNSFaithfulRangeQuotient
import InfoGeometry.Canonical.FilteredGNSRepresentedCStarClosure
import InfoGeometry.Canonical.FilteredGNSTomitaModularHilbertCompletion

/-!
# Filtered GNS boundary spine (finite → algebraic → range → closure)

This file packages the verified boundary corridor

`A_fin → A_alg → range(ρ) → closure(range(ρ))`

using only existing native owners and Mathlib structures.
It does not introduce a new algebra structure by analytic continuation.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSBoundarySpine

set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSFaithfulRangeQuotient
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion

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

/-- Finite stage into the algebraic star-colimit. -/
abbrev finiteToAlgebraic (i : I) :
    Stage i →⋆ₐ[ℂ] AlgebraicStarDirectLimit Stage sys :=
  algebraicStarDirectLimitOf Stage sys i

/-- Algebraic colimit onto the faithful represented operator range. -/
abbrev algebraicToRepresentedRange :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      representedAlgebraicRange Stage sys ω :=
  algebraicColimitRangeRestrict Stage sys ω

/-- Faithful represented range inclusion into the concrete represented
C-star closure. -/
abbrev representedRangeToClosure :
    representedAlgebraicRange Stage sys ω →⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω :=
  representedAlgebraicRangeInclusion Stage sys ω

/-- Algebraic colimit map directly into the represented C-star closure. -/
abbrev algebraicToRepresentedClosure :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      representedCStarClosure Stage sys ω :=
  algebraicColimitToRepresentedClosure Stage sys ω

/-- Finite stage map into the represented operator range. -/
abbrev finiteToRepresentedRange (i : I) :
    Stage i →⋆ₐ[ℂ] representedAlgebraicRange Stage sys ω :=
  (algebraicToRepresentedRange Stage sys ω).comp
    (finiteToAlgebraic Stage sys i)

/-- Finite stage map into the represented C-star closure. -/
abbrev finiteToRepresentedClosure (i : I) :
    Stage i →⋆ₐ[ℂ] representedCStarClosure Stage sys ω :=
  (algebraicToRepresentedClosure Stage sys ω).comp
    (finiteToAlgebraic Stage sys i)

@[simp] theorem finiteToRepresentedClosure_apply
    (i : I) (a : Stage i) :
    finiteToRepresentedClosure Stage sys ω i a =
      algebraicColimitToRepresentedClosure Stage sys ω
        (algebraicStarDirectLimitOf Stage sys i a) :=
  rfl

/-- On every finite-stage observable, the packaged spine map agrees with the
native global-stage representation in bounded operators. -/
@[simp] theorem finiteToRepresentedClosure_coe
    (i : I) (a : Stage i) :
    ((finiteToRepresentedClosure Stage sys ω i a :
        representedCStarClosure Stage sys ω) :
      GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω) =
      globalStageRepresentationStarAlgHom Stage sys ω i a := by
  calc
    ((finiteToRepresentedClosure Stage sys ω i a :
        representedCStarClosure Stage sys ω) :
      GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω)
        = algebraicColimitGNSRepresentation Stage sys ω
            (algebraicStarDirectLimitOf Stage sys i a) := by
            simp [finiteToRepresentedClosure, finiteToAlgebraic,
              algebraicToRepresentedClosure]
    _ = globalStageRepresentationStarAlgHom Stage sys ω i a :=
      algebraicColimitGNSRepresentation_of Stage sys ω i a

theorem algebraicToRepresentedClosure_denseRange :
    DenseRange (algebraicToRepresentedClosure Stage sys ω) :=
  algebraicColimitToRepresentedClosure_denseRange Stage sys ω

theorem representedRangeToClosure_denseRange :
    DenseRange (representedRangeToClosure Stage sys ω) :=
  representedAlgebraicRangeInclusion_denseRange Stage sys ω

/-- The closure layer is a native C-star algebra (concrete operator closure). -/
instance representedClosureCStarAlgebra :
    CStarAlgebra (representedCStarClosure Stage sys ω) :=
  representedCStarClosureCStarAlgebra (Stage := Stage) (sys := sys) (ω := ω)

variable
  (hclos :
    ∀ i,
      CStarStateColimit.Native.FilteredGNSTomitaClosability.IsClosableTomitaCore
        (ω.state i))

/-- The modular Hilbert completion lane is packaged separately from the
represented C-star closure lane. -/
abbrev modularHilbertCompletion : Type u :=
  ModularHilbertCompletion Stage sys ω hclos

theorem modularHilbertCompletion_completeSpace :
    CompleteSpace (modularHilbertCompletion Stage sys ω hclos) :=
  CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion.modularHilbertCompletion_complete
    Stage sys ω hclos

end CStarStateColimit.Native.FilteredGNSBoundarySpine
