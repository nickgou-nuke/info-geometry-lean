import InfoGeometry.Canonical.CuntzStarInductiveSystem
import InfoGeometry.Canonical.FilteredGNSHilbertColimit

/-!
# Cuntz GNS filtered Hilbert system

This module is the concrete categorical instantiation layer: a supplied
finite-stage C⋆ tower and a compatible family of states are fed to the native
filtered-GNS colimit.  No C⋆ completion or state family is asserted to exist
here; both remain explicit inputs.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzGNSFilteredSystem

open InfoGeometry.Canonical.CuntzStarInductiveSystem
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

def cuntzSystem : ContinuousStarInductiveSystem Stage :=
  CuntzStarTower.toContinuousStarInductiveSystem (Stage := Stage) T

variable
  (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
    Stage (cuntzSystem Stage T))

/-- The completed GNS space at the finite Cuntz stage `n`. -/
abbrev CuntzGNSStage (n : ℕ) : Type :=
  GNSStage Stage (cuntzSystem Stage T) ω n

/-- The Hilbert completion of the filtered Cuntz GNS system. -/
abbrev CuntzGNSHilbertColimit : Type :=
  GNSHilbertColimit Stage (cuntzSystem Stage T) ω

/-- Canonical stage embedding into the completed Cuntz GNS colimit. -/
def cuntzGNSStageToHilbertColimit (n : ℕ) :
    CuntzGNSStage Stage T ω n →ₗᵢ[ℂ]
  CuntzGNSHilbertColimit Stage T ω :=
  gnsStageToHilbertColimit Stage (cuntzSystem Stage T) ω n

@[simp] theorem cuntzGNSStageToHilbertColimit_transition
    {m n : ℕ} (hmn : m ≤ n)
    (x : CuntzGNSStage Stage T ω m) :
    cuntzGNSStageToHilbertColimit Stage T ω n
        (filteredGNSMap Stage (cuntzSystem Stage T) ω hmn x) =
      cuntzGNSStageToHilbertColimit Stage T ω m x := by
  exact gnsStageToHilbertColimit_transition
    Stage (cuntzSystem Stage T) ω hmn x

/-- The union of all finite-stage GNS images is dense in the colimit. -/
theorem dense_iUnion_range_cuntzGNSStageToHilbertColimit :
    Dense
      (⋃ n : ℕ,
        Set.range (cuntzGNSStageToHilbertColimit Stage T ω n)) :=
  dense_iUnion_range_gnsStageToHilbertColimit
    Stage (cuntzSystem Stage T) ω

/-- The Cuntz filtered GNS colimit is complete. -/
theorem cuntzGNSHilbertColimit_complete :
    CompleteSpace (CuntzGNSHilbertColimit Stage T ω) :=
  inferInstance

end InfoGeometry.Canonical.CuntzGNSFilteredSystem
