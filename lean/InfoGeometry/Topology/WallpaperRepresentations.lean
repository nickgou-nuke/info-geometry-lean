import Mathlib

/-!
# Wallpaper Group Representations

This module enumerates the 17 2D crystallographic (wallpaper) groups 
and provides the formal signature for classifying their irreducible 
representations via the little group method on the Brillouin zone.
-/

namespace InfoGeometry.Topology

/-- The 17 standard Wallpaper Groups (crystallographic groups of the plane) -/
inductive WallpaperGroup
  | p1 | p2 | pm | pg | cm
  | pmm | pmg | pgg | cmm
  | p4 | p4m | p4g
  | p3 | p3m1 | p31m
  | p6 | p6m
  deriving Repr, DecidableEq, Fintype

/-- The crystallographic point groups that occur as wallpaper holonomies. -/
inductive WallpaperPointGroup
  | C1 | C2 | D1 | V4 | C4 | D4 | C3 | D3 | C6 | D6
  deriving Repr, DecidableEq, Fintype

/-- The Bravais lattice family underlying a wallpaper group. -/
inductive WallpaperLattice
  | oblique | rectangular | rhombic | square | hexagonal
  deriving Repr, DecidableEq, Fintype

/-- Exactly seventeen wallpaper-group symbols are represented. -/
theorem wallpaperGroup_card : Fintype.card WallpaperGroup = 17 := by
  native_decide

/-- Bravais lattice family of each wallpaper group. -/
def latticeKind : WallpaperGroup → WallpaperLattice
  | .p1 | .p2 => .oblique
  | .pm | .pg | .pmm | .pmg | .pgg => .rectangular
  | .cm | .cmm => .rhombic
  | .p4 | .p4m | .p4g => .square
  | .p3 | .p3m1 | .p31m | .p6 | .p6m => .hexagonal

/-- Holonomy point group of each wallpaper group. -/
def pointGroupKind : WallpaperGroup → WallpaperPointGroup
  | .p1 => .C1
  | .p2 => .C2
  | .pm | .pg | .cm => .D1
  | .pmm | .pmg | .pgg | .cmm => .V4
  | .p4 => .C4
  | .p4m | .p4g => .D4
  | .p3 => .C3
  | .p3m1 | .p31m => .D3
  | .p6 => .C6
  | .p6m => .D6

/-- Order of the finite holonomy point group. -/
def pointGroupOrder : WallpaperPointGroup → ℕ
  | .C1 => 1
  | .C2 | .D1 => 2
  | .V4 | .C4 => 4
  | .D4 => 8
  | .C3 => 3
  | .D3 | .C6 => 6
  | .D6 => 12

/-- 
  The holonomy (point group) of each wallpaper group.
  The representations of the wallpaper group at the Γ-point (k=0)
  are isomorphic to the representations of this point group.
-/
def point_group_order : WallpaperGroup → ℕ
  | g => pointGroupOrder (pointGroupKind g)

/-- The order table is the point-group-kind order table. -/
theorem point_group_order_eq_kind_order (g : WallpaperGroup) :
    point_group_order g = pointGroupOrder (pointGroupKind g) := by
  rfl

/-- Finite complex irreducible dimension profile for a point group.

`oneDimensional` counts one-dimensional irreps and `twoDimensional` counts
two-dimensional irreps for the standard cyclic/dihedral wallpaper holonomies.
-/
structure IrrepDimensionProfile where
  oneDimensional : ℕ
  twoDimensional : ℕ
  total : ℕ
  deriving Repr, DecidableEq

/-- Standard finite point-group representation profiles over `ℂ`. -/
def pointGroupIrrepProfile : WallpaperPointGroup → IrrepDimensionProfile
  | .C1 => ⟨1, 0, 1⟩
  | .C2 | .D1 => ⟨2, 0, 2⟩
  | .V4 | .C4 => ⟨4, 0, 4⟩
  | .D4 => ⟨4, 1, 5⟩
  | .C3 => ⟨3, 0, 3⟩
  | .D3 => ⟨2, 1, 3⟩
  | .C6 => ⟨6, 0, 6⟩
  | .D6 => ⟨4, 2, 6⟩

/-- The degree-square sum of the listed irreps recovers the point-group order. -/
theorem pointGroupIrrepProfile_degree_square_sum (P : WallpaperPointGroup) :
    (pointGroupIrrepProfile P).oneDimensional
      + 4 * (pointGroupIrrepProfile P).twoDimensional = pointGroupOrder P := by
  cases P <;> rfl

/-- Total irreducible count at the Γ-point. -/
def gamma_irrep_count (g : WallpaperGroup) : ℕ :=
  (pointGroupIrrepProfile (pointGroupKind g)).total

/-- Γ-point representation profile obeys the finite point-group degree law. -/
theorem gamma_irrep_degree_square_sum (g : WallpaperGroup) :
    (pointGroupIrrepProfile (pointGroupKind g)).oneDimensional
      + 4 * (pointGroupIrrepProfile (pointGroupKind g)).twoDimensional =
        point_group_order g := by
  cases g <;> rfl

/-- The generic little group is the trivial point group `C1`. -/
def genericLittleGroupKind (_g : WallpaperGroup) : WallpaperPointGroup := .C1

/-- 
  The generic little group of a generic momentum vector `k` 
  in the Brillouin zone is always trivial (Z/1Z), meaning 
  all generic representations are 1-dimensional.
-/
def generic_little_group_order (g : WallpaperGroup) : ℕ :=
  pointGroupOrder (genericLittleGroupKind g)

/-- Generic momentum has trivial little-group order. -/
theorem generic_little_group_order_eq_one (g : WallpaperGroup) :
    generic_little_group_order g = 1 := by
  rfl

/-- Generic momentum has exactly one one-dimensional point-group irrep profile. -/
theorem generic_irrep_profile_one_dimensional (g : WallpaperGroup) :
    pointGroupIrrepProfile (genericLittleGroupKind g) = ⟨1, 0, 1⟩ := by
  rfl

/-- Example check: `p4m` has the `D4` Γ-point profile, four `1D` and one `2D`. -/
theorem p4m_gamma_irrep_profile :
    pointGroupIrrepProfile (pointGroupKind WallpaperGroup.p4m) = ⟨4, 1, 5⟩ := by
  rfl

/-- Example check: `p6m` has the `D6` Γ-point profile, four `1D` and two `2D`. -/
theorem p6m_gamma_irrep_profile :
    pointGroupIrrepProfile (pointGroupKind WallpaperGroup.p6m) = ⟨4, 2, 6⟩ := by
  rfl

end InfoGeometry.Topology
