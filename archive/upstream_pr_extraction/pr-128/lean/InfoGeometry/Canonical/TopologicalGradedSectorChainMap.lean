import InfoGeometry.Canonical.GradedRationalSectorCohomology
import InfoGeometry.Canonical.GradedRationalSectorChainMap

namespace InfoGeometry.Canonical

variable {V W : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]
  [∀ p, AddCommGroup (W p)]
  [∀ p, Module ℚ (W p)]

noncomputable def continuousSectorMapOnDegree
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) : S p →ₗ[ℚ] T p :=
  sectorMapOnDegree f p

@[simp] theorem continuousSectorMapOnDegree_apply
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) (x : S p) :
    continuousSectorMapOnDegree f p x = sectorMapOnDegree f p x :=
  rfl

theorem continuousSectorMapOnDegree_intertwines
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) (x : S p) :
    continuousSectorMapOnDegree f (p + 1)
        (restrictedDifferential D S hS p x) =
      restrictedDifferential E T hT p
        (continuousSectorMapOnDegree f p x) := by
  simpa using sectorMapOnDegree_intertwines_restrictedDifferential
    hS hT f p x

noncomputable def continuousSectorCycleMap
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) :
    sectorCycleSubmodule D S hS p →ₗ[ℚ]
      sectorCycleSubmodule E T hT p :=
  chainMapOnCycles
    (sectorDifferential D S hS)
    (sectorDifferential E T hT)
    (restrictedSectorChainMap hS hT f) p

@[simp] theorem continuousSectorCycleMap_apply
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) (x : sectorCycleSubmodule D S hS p) :
    continuousSectorCycleMap hS hT f p x =
      chainMapOnCycles
        (sectorDifferential D S hS)
        (sectorDifferential E T hT)
        (restrictedSectorChainMap hS hT f) p x :=
  rfl

end InfoGeometry.Canonical
