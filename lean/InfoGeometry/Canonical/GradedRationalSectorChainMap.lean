import InfoGeometry.Canonical.GradedRationalChainMap
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

variable {V W : ℕ → Type*}
  [∀ p, AddCommGroup (V p)]
  [∀ p, Module ℚ (V p)]
  [∀ p, AddCommGroup (W p)]
  [∀ p, Module ℚ (W p)]

/-- A chain map carrying one degreewise sector into another. -/
structure GradedRationalSectorChainMap
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    (S : GradedSector V)
    (T : GradedSector W) where
  toChainMap : GradedRationalChainMap D E
  preserves : ∀ p (x : V p), x ∈ S p → toChainMap.map p x ∈ T p

def sectorMapOnDegree
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) : S p →ₗ[ℚ] T p :=
  { toFun := fun x => ⟨f.toChainMap.map p x.1, f.preserves p x.1 x.2⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp
    map_smul' := by
      intro a x
      apply Subtype.ext
      simp }

theorem sectorMapOnDegree_intertwines_restrictedDifferential
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) (x : S p) :
    sectorMapOnDegree f (p + 1)
        (restrictedDifferential D S hS p x) =
      restrictedDifferential E T hT p (sectorMapOnDegree f p x) := by
  apply Subtype.ext
  exact f.toChainMap.commutes p x.1

def sectorDifferential
    (D : GradedRationalDifferential V)
    (S : GradedSector V)
    (hS : DifferentialPreservesSector D S) :
    GradedRationalDifferential (fun p => S p) where
  d := restrictedDifferential D S hS
  d_sq_zero := by
    intro p x
    exact restrictedDifferential_sq_zero D S hS p x

def restrictedSectorChainMap
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {S : GradedSector V} {T : GradedSector W}
    (hS : DifferentialPreservesSector D S)
    (hT : DifferentialPreservesSector E T)
    (f : GradedRationalSectorChainMap D E S T) :
    GradedRationalChainMap (sectorDifferential D S hS)
      (sectorDifferential E T hT) where
  map := sectorMapOnDegree f
  commutes := by
    intro p x
    exact sectorMapOnDegree_intertwines_restrictedDifferential hS hT f p x

def gradedSectorChainMapId
    (D : GradedRationalDifferential V)
    (S : GradedSector V) :
    GradedRationalSectorChainMap D D S S where
  toChainMap := gradedChainMapId D
  preserves := by
    intro p x hx
    exact hx

def gradedSectorChainMapComp
    {U : ℕ → Type*}
    [∀ p, AddCommGroup (U p)]
    [∀ p, Module ℚ (U p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {F : GradedRationalDifferential U}
    {S : GradedSector V} {T : GradedSector W} {R : GradedSector U}
    (f : GradedRationalSectorChainMap D E S T)
    (g : GradedRationalSectorChainMap E F T R) :
    GradedRationalSectorChainMap D F S R where
  toChainMap := gradedChainMapComp f.toChainMap g.toChainMap
  preserves := by
    intro p x hx
    exact g.preserves p (f.toChainMap.map p x) (f.preserves p x hx)

theorem sectorChainMap_preserves_cycles
    (D : GradedRationalDifferential V)
    (E : GradedRationalDifferential W)
    {S : GradedSector V} {T : GradedSector W}
    (f : GradedRationalSectorChainMap D E S T)
    (p : ℕ) {x : V p}
    (hx : x ∈ gradedCycleSubmodule D p)
    (hS : x ∈ S p) :
    f.toChainMap.map p x ∈ gradedCycleSubmodule E p ∧
    f.toChainMap.map p x ∈ T p := by
  exact ⟨chainMap_preserves_cycles D E f.toChainMap p hx,
    f.preserves p x hS⟩

theorem sectorChainMap_comp_preserves
    {U : ℕ → Type*}
    [∀ p, AddCommGroup (U p)]
    [∀ p, Module ℚ (U p)]
    {D : GradedRationalDifferential V}
    {E : GradedRationalDifferential W}
    {F : GradedRationalDifferential U}
    {S : GradedSector V} {T : GradedSector W} {R : GradedSector U}
    (f : GradedRationalSectorChainMap D E S T)
    (g : GradedRationalSectorChainMap E F T R)
    (p : ℕ) {x : V p} (hx : x ∈ S p) :
    (gradedSectorChainMapComp f g).toChainMap.map p x ∈ R p := by
  exact g.preserves p (f.toChainMap.map p x) (f.preserves p x hx)

end InfoGeometry.Canonical
