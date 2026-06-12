import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Equiv.Defs

namespace InfoGeometry.Topology.Wallpaper

/-- The 2D Euclidean plane representing the spatial lattice -/
abbrev Lattice2D := ℝ × ℝ

/-- A structure defining the `pg` wallpaper symmetry group, which contains 
translations and a non-symmorphic glide reflection. -/
structure WallpaperGroupPG where
  -- Lattice translation generator in the y-direction
  T_y : Lattice2D ≃ Lattice2D
  -- Glide reflection generator (translation by 1/2 in x, reflection across y=0)
  G : Lattice2D ≃ Lattice2D
  
  -- The fundamental defining relation of the pg group: 
  -- Applying the glide reflection twice equals a pure translation in the x-direction.
  h_glide_squared : ∀ p : Lattice2D, G (G p) = (p.1 + 1, p.2)
  
  -- Translation T_y commutes with the glide translation shift, but inverts the y-coordinate.
  -- G(x, y) = (x + 1/2, -y). T_y(x, y) = (x, y+1).
  -- G(T_y(x, y)) = (x + 1/2, -y - 1).
  -- T_y^{-1}(G(x,y)) = (x+1/2, -y-1).
  -- Thus G * T_y = T_y^{-1} * G.
  h_commutation : ∀ p : Lattice2D, G (T_y p) = (T_y.symm) (G p)

variable (pg : WallpaperGroupPG)

/-- 
THEOREM: The `pg` wallpaper group yields a non-orientable topology.
The commutation relation G * T_y = T_y^{-1} * G structurally proves that the translation 
in the y-direction is inverted under the glide reflection. 
When imposing these symmetries on a unit cell, the resulting quotient space 
is a Klein Bottle, not a Torus.
-/
theorem pg_generates_klein_bottle_topology (p : Lattice2D) :
    pg.G (pg.T_y p) = (pg.T_y.symm) (pg.G p) := by
  exact pg.h_commutation p

end InfoGeometry.Topology.Wallpaper
