import InfoGeometry.Canonical.FilteredGNSRepresentedCStarClosure
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# State/GNS bridge for the represented C⋆ closure

The filtered algebraic colimit first maps into the concrete represented
C⋆-closure (`representedCStarClosure`).  Any state on that completed carrier
then yields a native Mathlib GNS Hilbert completion and ⋆-representation.

This owner keeps the kernel-faithful quotient layer and the completion/state
layer separate: no unjustified identification with the raw colimit is made
without an injectivity hypothesis.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSRepresentedCStarStateCompletion

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredStarAlgebraDirectLimit
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open PositiveLinearMap
open scoped ComplexOrder

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

/-
Mathlib GNS needs order-theoretic structure on the represented C⋆-carrier.
When these instances are available, states and GNS are native.
-/
variable [PartialOrder (representedCStarClosure Stage sys ω)]
variable [StarOrderedRing (representedCStarClosure Stage sys ω)]

/-- Bundle for the represented C⋆-carrier states used by the completion layer. -/
abbrev RepresentedState : Type _ :=
  State (representedCStarClosure Stage sys ω)

/-- The positive linear functional underlying a represented state. -/
abbrev representedFunctional
    (ρ : State (representedCStarClosure Stage sys ω)) :
    representedCStarClosure Stage sys ω →ₚ[ℂ] ℂ :=
  ρ.functional

/-- Mathlib's pre-GNS carrier attached to a represented state. -/
abbrev representedPreGNS
    (ρ : State (representedCStarClosure Stage sys ω)) : Type _ :=
  PositiveLinearMap.PreGNS
    (representedFunctional (Stage := Stage) (sys := sys) (ω := ω) ρ)

/-- Mathlib's Hilbert completion attached to a represented state. -/
abbrev representedGNS
    (ρ : State (representedCStarClosure Stage sys ω)) : Type _ :=
  PositiveLinearMap.GNS
    (representedFunctional (Stage := Stage) (sys := sys) (ω := ω) ρ)

/-- Canonical dense map from pre-GNS carrier into the completed GNS space. -/
def representedPreGNSToGNS
    (ρ : State (representedCStarClosure Stage sys ω)) :
    representedPreGNS (Stage := Stage) (sys := sys) (ω := ω) ρ →
      representedGNS (Stage := Stage) (sys := sys) (ω := ω) ρ :=
  UniformSpace.Completion.coe'

theorem representedPreGNSToGNS_denseRange
    (ρ : State (representedCStarClosure Stage sys ω)) :
    DenseRange (representedPreGNSToGNS (Stage := Stage) (sys := sys) (ω := ω) ρ) :=
  UniformSpace.Completion.denseRange_coe

theorem representedPreGNSToGNS_isometry
    (ρ : State (representedCStarClosure Stage sys ω)) :
    Isometry (representedPreGNSToGNS (Stage := Stage) (sys := sys) (ω := ω) ρ) :=
  UniformSpace.Completion.coe_isometry

theorem representedGNS_complete
    (ρ : State (representedCStarClosure Stage sys ω)) :
    CompleteSpace (representedGNS (Stage := Stage) (sys := sys) (ω := ω) ρ) :=
  inferInstance

/-- Native GNS ⋆-representation on the represented C⋆-closure. -/
abbrev representedGNSStarAlgHom
    (ρ : State (representedCStarClosure Stage sys ω)) :
    representedCStarClosure Stage sys ω →⋆ₐ[ℂ]
      (representedGNS (Stage := Stage) (sys := sys) (ω := ω) ρ →L[ℂ]
        representedGNS (Stage := Stage) (sys := sys) (ω := ω) ρ) :=
  (representedFunctional (Stage := Stage) (sys := sys) (ω := ω) ρ).gnsStarAlgHom

/-- Algebraic colimit representation obtained by composing with the represented
C⋆-closure inclusion map. -/
def algebraicColimitToRepresentedGNS
    (ρ : State (representedCStarClosure Stage sys ω)) :
    AlgebraicStarDirectLimit Stage sys →⋆ₐ[ℂ]
      (representedGNS (Stage := Stage) (sys := sys) (ω := ω) ρ →L[ℂ]
        representedGNS (Stage := Stage) (sys := sys) (ω := ω) ρ) :=
  (representedGNSStarAlgHom (Stage := Stage) (sys := sys) (ω := ω) ρ).comp
    (algebraicColimitToRepresentedClosure Stage sys ω)

@[simp] theorem algebraicColimitToRepresentedGNS_apply
    (ρ : State (representedCStarClosure Stage sys ω))
    (a : AlgebraicStarDirectLimit Stage sys) :
    algebraicColimitToRepresentedGNS (Stage := Stage) (sys := sys) (ω := ω) ρ a =
      representedGNSStarAlgHom (Stage := Stage) (sys := sys) (ω := ω) ρ
        (algebraicColimitToRepresentedClosure Stage sys ω a) :=
  rfl

end CStarStateColimit.Native.FilteredGNSRepresentedCStarStateCompletion
