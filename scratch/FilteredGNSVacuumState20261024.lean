/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Canonical.FilteredGNSVacuumReadback
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Spectral-order vacuum state on the existing represented C⋆ closure

Uncompiled consumer of the planned native readback base. The local order is
Mathlib's constructed spectral order, not an additional hypothesis. Positivity
reduces to square decomposition and the base's proved vector-functional
star-square positivity. No new carrier or state-witness package is introduced.
-/

noncomputable section
namespace CStarStateColimit.Native.FilteredGNSVacuumState

open CStarStateColimit.Native
open FilteredGNSHilbertColimit FilteredGNSHilbertNontrivial
open FilteredGNSGlobalStageRepresentation FilteredGNSRepresentedCStarClosure
open FilteredGNSVacuumReadback
open scoped InnerProductSpace ComplexOrder

universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

local instance representedSpectralOrder :
    PartialOrder (representedCStarClosure Stage sys ω) :=
  CStarAlgebra.spectralOrder (representedCStarClosure Stage sys ω)

local instance representedSpectralStarOrderedRing :
    StarOrderedRing (representedCStarClosure Stage sys ω) :=
  CStarAlgebra.spectralOrderedRing (representedCStarClosure Stage sys ω)

/-- Positivity follows from the closure's spectral order and actual squares. -/
def representedVacuumPositiveFunctional (i : I) :
    representedCStarClosure Stage sys ω →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (representedVacuumFunctional Stage sys ω i).toLinearMap (by
    intro a ha
    obtain ⟨b, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
    exact representedVacuumFunctional_star_mul_self Stage sys ω i b)

/-- Native normalized State, with no assumed positivity or normalization fields. -/
def representedVacuumState (i : I) : State (representedCStarClosure Stage sys ω) where
  functional := representedVacuumPositiveFunctional Stage sys ω i
  normalized := representedVacuumFunctional_one Stage sys ω i

/-- Every represented stage observable recovers its prescribed compatible state. -/
theorem representedVacuumState_stage (i j : I) (a : Stage j) :
    (representedVacuumState Stage sys ω i).functional
      ⟨globalStageRepresentationStarAlgHom Stage sys ω j a,
        globalStageRepresentation_mem_representedCStarClosure Stage sys ω j a⟩ =
      (ω.state j).functional a := by
  exact representedVacuumFunctional_stage Stage sys ω i j a

/-- Choice of vacuum stage does not change the state on any element of the closure. -/
theorem representedVacuumState_eq (i j : I) :
    representedVacuumState Stage sys ω i = representedVacuumState Stage sys ω j := by
  apply State.ext
  apply PositiveLinearMap.ext
  intro a
  change ⟪globalGNSVacuum Stage sys ω i,
      (a : GNSHilbertColimit Stage sys ω →L[ℂ] GNSHilbertColimit Stage sys ω)
        (globalGNSVacuum Stage sys ω i)⟫_ℂ =
    ⟪globalGNSVacuum Stage sys ω j,
      (a : GNSHilbertColimit Stage sys ω →L[ℂ] GNSHilbertColimit Stage sys ω)
        (globalGNSVacuum Stage sys ω j)⟫_ℂ
  rw [globalGNSVacuum_eq Stage sys ω i j]

end CStarStateColimit.Native.FilteredGNSVacuumState
