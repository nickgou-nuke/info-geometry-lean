import InfoGeometry.Canonical.GradedRationalSectorChainMap

namespace InfoGeometry.Canonical

variable {V : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]
variable {W : ℕ → Type*}
  [∀ p, AddCommGroup (W p)]
  [∀ p, Module ℚ (W p)]

def sectorCycleSubmodule
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) : Submodule ℚ (S p) :=
  LinearMap.ker (restrictedDifferential D S hS p)

def sectorBoundarySubmodule
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) : Submodule ℚ (S (p + 1)) :=
  LinearMap.range (restrictedDifferential D S hS p)

theorem sectorBoundary_le_cycle
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) :
    sectorBoundarySubmodule D S hS p ≤
      sectorCycleSubmodule D S hS (p + 1) := by
  rintro x ⟨y, rfl⟩
  exact restrictedDifferential_sq_zero D S hS p y

def sectorBoundaryInCycles
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) :
    Submodule ℚ (sectorCycleSubmodule D S hS (p + 1)) :=
  (sectorBoundarySubmodule D S hS p).comap
    (Submodule.subtype (sectorCycleSubmodule D S hS (p + 1)))

def sectorCohomologyShadow
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) :=
  sectorCycleSubmodule D S hS (p + 1) ⧸
    sectorBoundaryInCycles D S hS p

instance sectorCohomologyShadow.instAddCommGroup
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) :
    AddCommGroup (sectorCohomologyShadow D S hS p) := by
  dsimp [sectorCohomologyShadow]
  infer_instance

instance sectorCohomologyShadow.instModule
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S)
    (p : ℕ) :
    Module ℚ (sectorCohomologyShadow D S hS p) := by
  dsimp [sectorCohomologyShadow]
  infer_instance

def sectorCohomologyMap
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) :
    sectorCohomologyShadow D S hS p →ₗ[ℚ]
      sectorCohomologyShadow E T hT p :=
  chainMapOnCohomology
    (sectorDifferential D S hS)
    (sectorDifferential E T hT)
    (restrictedSectorChainMap hS hT f) p

@[simp]
theorem sectorCohomologyMap_mk
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) (x : sectorCycleSubmodule D S hS (p + 1)) :
    sectorCohomologyMap hS hT f p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (M := sectorCycleSubmodule E T hT (p + 1))
        (p := sectorBoundaryInCycles E T hT p)
        (⟨sectorMapOnDegree f (p + 1) x, by
          change restrictedDifferential E T hT (p + 1)
              (sectorMapOnDegree f (p + 1) x) = 0
          rw [← sectorMapOnDegree_intertwines_restrictedDifferential
            hS hT f (p + 1) x.1]
          simp [x.2]⟩) := by
  exact chainMapOnCohomology_mk
    (sectorDifferential D S hS)
    (sectorDifferential E T hT)
    (restrictedSectorChainMap hS hT f)
    p x

end InfoGeometry.Canonical
