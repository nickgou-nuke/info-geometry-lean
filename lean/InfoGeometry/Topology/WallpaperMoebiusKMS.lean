import Mathlib

/-!
# Wallpaper Groups, the KMS Stripe, and the Möbius Tape

This module formalizes the geometric construction of the thermal cylinder 
(the 0 to β stripe) from a 2D wallpaper group, and the topological 
quotient that produces the Möbius symmetry tape.
-/

namespace InfoGeometry

/-- The fundamental domain of the KMS state: a stripe in the complex plane. -/
structure KMSStripe where
  beta : ℝ
  h_beta : 0 < beta

/-- 
  The Wallpaper lattice translations in 2D Euclidean space.
  T_space translates along the spatial dimension (L).
  T_time translates along the thermal/imaginary-time dimension (β).
-/
def T_space (L x y : ℝ) : ℝ × ℝ := (x + L, y)
def T_time (β x y : ℝ) : ℝ × ℝ := (x, y + β)

/-- The standard thermal cylinder glues the spatial coordinate periodically. -/
def cylinder_gluing (L x y : ℝ) : ℝ × ℝ := (x + L, y)

/-- 
  The Möbius tape gluing involves a spatial translation and a parity inversion 
  in the thermal coordinate: y ↦ β - y. 
  This enforces the orientation-reversing boundary condition (cross-cap).
-/
def moebius_gluing (L β x y : ℝ) : ℝ × ℝ := (x + L, β - y)

/-- 
  Theorem: Applying the Möbius gluing twice yields a pure spatial translation 
  of 2L, which corresponds to the orientable double cover (the two p-tapes).
-/
theorem moebius_double_cover (L β x y : ℝ) :
    let (x1, y1) := moebius_gluing L β x y
    let (x2, y2) := moebius_gluing L β x1 y1
    (x2, y2) = (x + 2 * L, y) := by
  dsimp [moebius_gluing]
  ext
  · ring
  · ring

end InfoGeometry
