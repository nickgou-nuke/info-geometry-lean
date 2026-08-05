import InfoGeometry.Canonical.TopologicalGradedSectorChainMap
import InfoGeometry.Canonical.GradedRationalSectorCohomologyTopological

/-!
  Continuous cohomology maps for sector chain maps.  The quotient-invariance
  hypothesis is explicit: it is the precise descent condition and is not
  inferred merely from continuity.
-/

noncomputable section

namespace InfoGeometry.Canonical

variable {V W : ℕ → Type*}
  [∀ p, NormedAddCommGroup (V p)]
  [∀ p, NormedSpace ℚ (V p)]
  [∀ p, FiniteDimensional ℚ (V p)]
  [∀ p, NormedAddCommGroup (W p)]
  [∀ p, NormedSpace ℚ (W p)]
  [∀ p, FiniteDimensional ℚ (W p)]

def continuousSectorCohomologyMap
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ)
    (hInvariant : ∀ a b : sectorCycleSubmodule D S hS (p + 1),
      (sectorBoundaryInCycles D S hS p).quotientRel a b →
        sectorCohomologyQuotientMk E T hT p
      (continuousSectorCycleMap hS hT f (p + 1) a) =
          sectorCohomologyQuotientMk E T hT p
            (continuousSectorCycleMap hS hT f (p + 1) b)) :
    sectorCohomologyShadow D S hS p →
      sectorCohomologyShadow E T hT p :=
  sectorCohomologyQuotientLift D E S T hS hT p
    (continuousSectorCycleMap hS hT f (p + 1)) hInvariant

@[simp] theorem continuousSectorCohomologyMap_mk
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ)
    (hInvariant : ∀ a b : sectorCycleSubmodule D S hS (p + 1),
      (sectorBoundaryInCycles D S hS p).quotientRel a b →
        sectorCohomologyQuotientMk E T hT p
            (continuousSectorCycleMap hS hT f (p + 1) a) =
          sectorCohomologyQuotientMk E T hT p
            (continuousSectorCycleMap hS hT f (p + 1) b))
    (x : sectorCycleSubmodule D S hS (p + 1)) :
    continuousSectorCohomologyMap hS hT f p hInvariant
        (Submodule.Quotient.mk x) =
      sectorCohomologyQuotientMk E T hT p
        (continuousSectorCycleMap hS hT f (p + 1) x) := by
  rfl

end InfoGeometry.Canonical
