import Mathlib.Tactic

/-!
# InfoGeometry.Projective.Quadrics.AffineSlices

Affine-slice lemmas for the standard quadratic surfaces used as charts in
projective geometry:

* ellipsoids,
* hyperboloids,
* paraboloids.

The point of this file is narrow and theorem-honest:

* each affine surface is the `w = 1` chart of an explicit homogeneous quadric;
* each homogeneous quadric is invariant under nonzero scaling of homogeneous
  coordinates;
* this does **not** prove that the three affine surfaces are equal as orthogonal
  coordinate systems.

No quotient construction.
No classification theorem.
No `sorry`.
-/

namespace InfoGeometry.Projective.Quadrics.AffineSlices

variable {R : Type*} [CommRing R]

/-- Homogeneous coordinates in `R⁴`. -/
structure HomPoint4 (R : Type*) where
  x : R
  y : R
  z : R
  w : R

namespace HomPoint4

variable {R : Type*} [CommRing R]

/-- Uniform scaling of homogeneous coordinates. -/
def scale (l : R) (P : HomPoint4 R) : HomPoint4 R where
  x := l * P.x
  y := l * P.y
  z := l * P.z
  w := l * P.w

end HomPoint4

/-- Homogeneous quadric for the ellipsoid / two-sheet chart. -/
def ellipsoidHom (P : HomPoint4 R) : R :=
  P.x ^ 2 + P.y ^ 2 + P.z ^ 2 - P.w ^ 2

/-- Homogeneous quadric for the one-sheet hyperboloid chart. -/
def hyperboloidHom (P : HomPoint4 R) : R :=
  P.x ^ 2 + P.y ^ 2 - P.z ^ 2 - P.w ^ 2

/-- Homogeneous quadric for the paraboloid chart. -/
def paraboloidHom (P : HomPoint4 R) : R :=
  P.x ^ 2 + P.y ^ 2 - P.z * P.w

/-- The ellipsoid affine chart `x² + y² + z² = 1`. -/
def ellipsoidAff (x y z : R) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 = 1

/-- The one-sheet hyperboloid affine chart `x² + y² - z² = 1`. -/
def hyperboloidAff (x y z : R) : Prop :=
  x ^ 2 + y ^ 2 - z ^ 2 = 1

/-- The paraboloid affine chart `z = x² + y²`. -/
def paraboloidAff (x y z : R) : Prop :=
  z = x ^ 2 + y ^ 2

/-- Scaling the homogeneous ellipsoid quadric scales it by `l²`. -/
theorem ellipsoidHom_scale (l : R) (P : HomPoint4 R) :
    ellipsoidHom (HomPoint4.scale l P) = l ^ 2 * ellipsoidHom P := by
  rcases P with ⟨x, y, z, w⟩
  unfold HomPoint4.scale ellipsoidHom
  ring

/-- Scaling the homogeneous hyperboloid quadric scales it by `l²`. -/
theorem hyperboloidHom_scale (l : R) (P : HomPoint4 R) :
    hyperboloidHom (HomPoint4.scale l P) = l ^ 2 * hyperboloidHom P := by
  rcases P with ⟨x, y, z, w⟩
  unfold HomPoint4.scale hyperboloidHom
  ring

/-- Scaling the homogeneous paraboloid quadric scales it by `l²`. -/
theorem paraboloidHom_scale (l : R) (P : HomPoint4 R) :
    paraboloidHom (HomPoint4.scale l P) = l ^ 2 * paraboloidHom P := by
  rcases P with ⟨x, y, z, w⟩
  unfold HomPoint4.scale paraboloidHom
  ring

/-- Nonzero scaling does not change whether a point lies on the ellipsoid quadric. -/
theorem ellipsoidHom_scale_iff
    [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0) (P : HomPoint4 R) :
    ellipsoidHom (HomPoint4.scale l P) = 0 ↔ ellipsoidHom P = 0 := by
  constructor
  · intro h
    rw [ellipsoidHom_scale] at h
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
    exact (mul_eq_zero.mp h).resolve_left hl2
  · intro h
    rw [ellipsoidHom_scale, h, mul_zero]

/-- Nonzero scaling does not change whether a point lies on the hyperboloid quadric. -/
theorem hyperboloidHom_scale_iff
    [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0) (P : HomPoint4 R) :
    hyperboloidHom (HomPoint4.scale l P) = 0 ↔ hyperboloidHom P = 0 := by
  constructor
  · intro h
    rw [hyperboloidHom_scale] at h
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
    exact (mul_eq_zero.mp h).resolve_left hl2
  · intro h
    rw [hyperboloidHom_scale, h, mul_zero]

/-- Nonzero scaling does not change whether a point lies on the paraboloid quadric. -/
theorem paraboloidHom_scale_iff
    [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0) (P : HomPoint4 R) :
    paraboloidHom (HomPoint4.scale l P) = 0 ↔ paraboloidHom P = 0 := by
  constructor
  · intro h
    rw [paraboloidHom_scale] at h
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
    exact (mul_eq_zero.mp h).resolve_left hl2
  · intro h
    rw [paraboloidHom_scale, h, mul_zero]

/-- The `w = 1` chart of the ellipsoid quadric is the affine ellipsoid equation. -/
theorem ellipsoidAff_iff_homogeneous_one (x y z : R) :
    ellipsoidAff x y z ↔ ellipsoidHom (⟨x, y, z, (1 : R)⟩) = 0 := by
  constructor
  · intro h
    unfold ellipsoidAff ellipsoidHom at *
    rw [h]
    ring
  · intro h
    simpa [ellipsoidAff, ellipsoidHom] using (sub_eq_zero.mp h)

/-- The `w = 1` chart of the hyperboloid quadric is the affine hyperboloid equation. -/
theorem hyperboloidAff_iff_homogeneous_one (x y z : R) :
    hyperboloidAff x y z ↔ hyperboloidHom (⟨x, y, z, (1 : R)⟩) = 0 := by
  constructor
  · intro h
    unfold hyperboloidAff hyperboloidHom at *
    rw [h]
    ring
  · intro h
    simpa [hyperboloidAff, hyperboloidHom] using (sub_eq_zero.mp h)

/-- The `w = 1` chart of the paraboloid quadric is the affine paraboloid equation. -/
theorem paraboloidAff_iff_homogeneous_one (x y z : R) :
    paraboloidAff x y z ↔ paraboloidHom (⟨x, y, z, (1 : R)⟩) = 0 := by
  constructor
  · intro h
    unfold paraboloidAff paraboloidHom at *
    rw [h]
    ring
  · intro h
    simpa [paraboloidAff, paraboloidHom] using (sub_eq_zero.mp h).symm

end InfoGeometry.Projective.Quadrics.AffineSlices
