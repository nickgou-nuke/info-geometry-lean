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