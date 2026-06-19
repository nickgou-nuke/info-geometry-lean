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
  deriving Repr, DecidableEq

/-- 
  The holonomy (point group) of each wallpaper group.
  The representations of the wallpaper group at the Γ-point (k=0)
  are isomorphic to the representations of this point group.
-/
def point_group_order : WallpaperGroup → ℕ
  | .p1 => 1
  | .p2 | .pm | .pg | .cm => 2
  | .pmm | .pmg | .pgg | .cmm => 4
  | .p4 => 4
  | .p4m | .p4g => 8
  | .p3 => 3
  | .p3m1 | .p31m => 6
  | .p6 => 6
  | .p6m => 12

/-- 
  The generic little group of a generic momentum vector `k` 
  in the Brillouin zone is always trivial (Z/1Z), meaning 
  all generic representations are 1-dimensional.
-/
def generic_little_group_order (g : WallpaperGroup) : ℕ := 1

end InfoGeometry.Topology
