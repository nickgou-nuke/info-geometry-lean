import InfoGeometry.Canonical.FilteredIsometricHilbertCompletion
import InfoGeometry.Canonical.FilteredGNSTomitaModularForm

/-!
# Native filtered GNS Hilbert colimit

The completed GNS spaces of a compatible filtered family of noncommutative
states form a coherent system of complex linear isometries.  This file
instantiates the generic filtered Hilbert-colimit owner and obtains a complete
Hilbert space generated densely by the stage GNS images.

The construction does not choose coordinates, an ambient representation, or
a scalar/diagonal replacement for the stage algebras.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSHilbertColimit

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

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

local notation "G" =>
  fun i => (ω.state i).functional.GNS

/-- The filtered completed-GNS transitions bundled as a coherent isometric
direct system.  Identity and composition are inherited from the native GNS
transport theorems, not postulated as compatibility fields. -/
def filteredGNSIsometricDirectSystem :
    IsometricDirectSystem G where
  map := fun hij =>
    filteredGNSLinearIsometry Stage sys ω hij
  map_id := by
    intro i
    ext x
    rw [filteredGNSLinearIsometry_apply]
    exact congrFun
      (filteredGNSMap_id Stage sys ω i) x
  map_comp := by
    intro i j k hij hjk
    ext x
    change
      filteredGNSMap Stage sys ω hjk
          (filteredGNSMap Stage sys ω hij x) =
        filteredGNSMap Stage sys ω
          (le_trans hij hjk) x
    exact congrFun
      (filteredGNSMap_comp Stage sys ω hij hjk) x

/-- Algebraic filtered colimit of the completed stage GNS spaces. -/
abbrev AlgebraicGNSHilbertColimit : Type u :=
  RealDirectLimit G
    (filteredGNSIsometricDirectSystem Stage sys ω)

/-- Hilbert completion of the filtered GNS direct limit. -/
abbrev GNSHilbertColimit : Type u :=
  HilbertDirectLimit G
    (filteredGNSIsometricDirectSystem Stage sys ω)

/-- Canonical complex linear isometry from a stage GNS space into the
completed filtered GNS colimit. -/
def gnsStageToHilbertColimit
    (i : I) :
    (ω.state i).functional.GNS →ₗᵢ[ℂ]
      GNSHilbertColimit Stage sys ω :=
  stageToHilbertDirectLimit G
    (filteredGNSIsometricDirectSystem Stage sys ω) i

@[simp] theorem gnsStageToHilbertColimit_transition
    {i j : I} (hij : i ≤ j)
    (x : (ω.state i).functional.GNS) :
    gnsStageToHilbertColimit Stage sys ω j
        (filteredGNSMap Stage sys ω hij x) =
      gnsStageToHilbertColimit Stage sys ω i x := by
  exact
    stageToHilbertDirectLimit_transition G
      (filteredGNSIsometricDirectSystem Stage sys ω)
      hij x

/-- The union of the noncommutative stage GNS images is dense in the completed
filtered GNS Hilbert colimit. -/
theorem dense_iUnion_range_gnsStageToHilbertColimit :
    Dense
      (⋃ i : I,
        Set.range
          (gnsStageToHilbertColimit Stage sys ω i)) :=
  dense_iUnion_range_stageToHilbertDirectLimit G
    (filteredGNSIsometricDirectSystem Stage sys ω)

/-- The filtered GNS Hilbert colimit is complete. -/
theorem gnsHilbertColimit_complete :
    CompleteSpace (GNSHilbertColimit Stage sys ω) :=
  inferInstance

end CStarStateColimit.Native.FilteredGNSHilbertColimit
