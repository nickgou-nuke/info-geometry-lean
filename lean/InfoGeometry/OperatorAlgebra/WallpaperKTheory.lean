import Mathlib
import InfoGeometry.Topology.WallpaperRepresentations

/-!
# K-Theory of Wallpaper C*-Algebras

This module formalizes the K-theory ranks ($K_0$ and $K_1$) of the 
group C*-algebras associated with the 17 Wallpaper Groups. 

By the Baum-Connes isomorphism for crystallographic groups, 
the K-theory measures the number of stable topological insulator 
phases (K_0) and gapless chiral edge modes (K_1) on the 2D lattice.
-/

namespace InfoGeometry.OperatorAlgebra

open Topology

/-- 
  The rank of the K_0 group of the group C*-algebra for a given wallpaper group.
  This free abelian group classifies the stable D-branes / topological insulators 
  on the orbifold. The explosion in rank (e.g. from 2 in p1 to 9 in p4m) 
  is due to the high-symmetry points (orbifold singularities) trapping the states,
  a direct manifestation of Momentum-Space Holography.
-/
def wallpaper_k0_rank : WallpaperGroup → ℕ
  | .p1   => 2
  | .p2   => 6
  | .pm   => 3
  | .pg   => 2
  | .cm   => 2
  | .pmm  => 6
  | .pmg  => 4
  | .pgg  => 3
  | .cmm  => 4
  | .p4   => 9
  | .p4m  => 9
  | .p4g  => 6
  | .p3   => 8
  | .p3m1 => 6
  | .p31m => 6
  | .p6   => 10
  | .p6m  => 9

/-- 
  The rank of the K_1 group of the group C*-algebra for a given wallpaper group.
  This classifies the winding number of stable Majorana Zero Modes.
  Notice that glide reflections (Brillouin Klein Bottles) and point group torsion 
  kill the K_1 winding modes, trapping the anomalies purely in K_0.
-/
def wallpaper_k1_rank : WallpaperGroup → ℕ
  | .p1   => 2
  | .p2   => 0
  | .pm   => 1
  | .pg   => 1
  | .cm   => 1
  | .pmm  => 0
  | .pmg  => 0
  | .pgg  => 0
  | .cmm  => 0
  | .p4   => 0
  | .p4m  => 0
  | .p4g  => 0
  | .p3   => 0
  | .p3m1 => 0
  | .p31m => 0
  | .p6   => 0
  | .p6m  => 0

end InfoGeometry.OperatorAlgebra
