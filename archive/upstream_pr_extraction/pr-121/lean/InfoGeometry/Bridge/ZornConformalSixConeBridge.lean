import Mathlib.Tactic

import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import InfoGeometry.Canonical.PauliHestenesSpinMomentum
import InfoGeometry.Projective.KleinQuadric

/-!
# Zorn conformal six-cone bridge

This file extracts a concrete real `(2,4)` coordinate slice from the repository's
existing `PACSplit44` carrier and proves the Dirac six-cone embedding of a
Pauli paravector is null.

The real `(2,4)` form is not identified with the real Plücker form, whose
signature is `(3,3)`.  Instead, an explicit complex coordinate transform is
given and proved to carry the `(2,4)` polynomial to the complex Klein
quadratic polynomial.  Thus the Klein correspondence asserted here is an
algebraic statement after complexification.

No orthogonal-group classification, spin-group isomorphism, topological
compactification, or twistor-incidence theorem is inferred from these
coordinate identities.
-/

noncomputable section

namespace InfoGeometry.Bridge.ZornConformalSixCone

open ProjectiveAffineConformalClosure55
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Projective.KleinQuadric

/-- Coordinates `(A₀,B_z | A_x,A_y,A_z,B₀)` on the conformal six-space. -/
structure ConformalSix where
  a0 : ℝ
  ax : ℝ
  ay : ℝ
  az : ℝ
  b0 : ℝ
  bz : ℝ

/-- The diagonal quadratic polynomial of signature `(2,4)`. -/
def quadratic24 (X : ConformalSix) : ℝ :=
  X.a0 ^ 2 + X.bz ^ 2 -
    (X.ax ^ 2 + X.ay ^ 2 + X.az ^ 2 + X.b0 ^ 2)

/--
Insert the conformal six-space into the existing split `(4,4)` carrier.

The coordinate convention is
`x=(A₀,B_x,B_y,B_z)`, `y=(B₀,A_x,A_y,A_z)`, with `B_x=B_y=0`.
-/
def toPACSplit44 (X : ConformalSix) : PACSplit44 where
  x0 := X.a0
  x1 := 0
  x2 := 0
  x3 := X.bz
  y0 := X.b0
  y1 := X.ax
  y2 := X.ay
  y3 := X.az

/-- The image is exactly the transverse-axial frozen slice. -/
theorem toPACSplit44_transverse_axial_frozen (X : ConformalSix) :
    (toPACSplit44 X).x1 = 0 ∧ (toPACSplit44 X).x2 = 0 := by
  exact ⟨rfl, rfl⟩

/-- Restriction of the repository's `Q44` is the desired `Q24` polynomial. -/
@[simp]
theorem Q44_toPACSplit44 (X : ConformalSix) :
    Q44 (toPACSplit44 X) = quadratic24 X := by
  simp [Q44, toPACSplit44, quadratic24]
  ring

/-- Scalar multiplication on conformal six-coordinates. -/
def scale (c : ℝ) (X : ConformalSix) : ConformalSix where
  a0 := c * X.a0
  ax := c * X.ax
  ay := c * X.ay
  az := c * X.az
  b0 := c * X.b0
  bz := c * X.bz

/-- The six-dimensional quadratic form is homogeneous of degree two. -/
theorem quadratic24_scale (c : ℝ) (X : ConformalSix) :
    quadratic24 (scale c X) = c ^ 2 * quadratic24 X := by
  cases X
  simp [quadratic24, scale]
  ring

/--
Dirac's affine-chart embedding of a Minkowski paravector into the six-cone.

The parameter `kappa` is the homogeneous ray scale.
-/
def diracConeEmbedding (kappa : ℝ) (P : PauliParavector) : ConformalSix where
  a0 := kappa * P.energy
  ax := kappa * P.px
  ay := kappa * P.py
  az := kappa * P.pz
  b0 := kappa * (1 + P.minkowskiNormSq) / 2
  bz := kappa * (1 - P.minkowskiNormSq) / 2

/-- The affine gauge coordinate is exactly the homogeneous scale. -/
@[simp]
theorem diracConeEmbedding_affine_gauge
    (kappa : ℝ) (P : PauliParavector) :
    (diracConeEmbedding kappa P).b0 +
      (diracConeEmbedding kappa P).bz = kappa := by
  simp [diracConeEmbedding]
  ring

/-- The complementary cone coordinate recovers the scaled Minkowski norm. -/
@[simp]
theorem diracConeEmbedding_complementary_gauge
    (kappa : ℝ) (P : PauliParavector) :
    (diracConeEmbedding kappa P).b0 -
      (diracConeEmbedding kappa P).bz =
        kappa * P.minkowskiNormSq := by
  simp [diracConeEmbedding]
  ring

/-- The Dirac affine-chart formula lands identically on the real six-cone. -/
theorem diracConeEmbedding_null
    (kappa : ℝ) (P : PauliParavector) :
    quadratic24 (diracConeEmbedding kappa P) = 0 := by
  simp [quadratic24, diracConeEmbedding, PauliParavector.minkowskiNormSq]
  ring

/-- The same nullity statement read back through the canonical `PACSplit44`. -/
theorem diracConeEmbedding_PACSplit44_null
    (kappa : ℝ) (P : PauliParavector) :
    Q44 (toPACSplit44 (diracConeEmbedding kappa P)) = 0 := by
  rw [Q44_toPACSplit44, diracConeEmbedding_null]

/-- Changing the ray scale is ordinary homogeneous rescaling. -/
theorem diracConeEmbedding_scale
    (c kappa : ℝ) (P : PauliParavector) :
    diracConeEmbedding (c * kappa) P =
      scale c (diracConeEmbedding kappa P) := by
  cases P
  ext <;>
    simp [diracConeEmbedding, scale, PauliParavector.minkowskiNormSq] <;>
    ring

/-- Read the Minkowski point from the unit affine chart. -/
def affineReadback (X : ConformalSix) : PauliParavector where
  energy := X.a0
  px := X.ax
  py := X.ay
  pz := X.az

/-- Unit-scale Dirac embedding retains every Minkowski coordinate. -/
@[simp]
theorem affineReadback_diracConeEmbedding_one (P : PauliParavector) :
    affineReadback (diracConeEmbedding 1 P) = P := by
  cases P
  rfl

/-- Consequently the unit affine chart is injective. -/
theorem diracConeEmbedding_one_injective :
    Function.Injective (diracConeEmbedding 1) :=
  Function.LeftInverse.injective affineReadback_diracConeEmbedding_one

/--
Complex Plücker coordinates for the conformal six-vector.

The factor `i` in the `(A_x,A_y)` pair is essential: over the reals the
Klein form has signature `(3,3)`, not `(2,4)`.
-/
def toComplexPlucker (X : ConformalSix) : Plucker6 ℂ where
  p01 := ((X.a0 + X.b0 : ℝ) : ℂ)
  p02 := (X.ax : ℂ) + Complex.I * (X.ay : ℂ)
  p03 := ((X.bz + X.az : ℝ) : ℂ)
  p12 := ((X.bz - X.az : ℝ) : ℂ)
  p13 := (X.ax : ℂ) - Complex.I * (X.ay : ℂ)
  p23 := ((X.a0 - X.b0 : ℝ) : ℂ)

/-- The complex Klein polynomial is exactly the complexified `Q24` form. -/
theorem kleinQ_toComplexPlucker (X : ConformalSix) :
    Plucker6.kleinQ (toComplexPlucker X) = (quadratic24 X : ℂ) := by
  simp [Plucker6.kleinQ, toComplexPlucker, quadratic24]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Every Dirac-cone point therefore determines a point of the complex Klein cone. -/
theorem diracConeEmbedding_isKlein
    (kappa : ℝ) (P : PauliParavector) :
    Plucker6.IsKlein (toComplexPlucker (diracConeEmbedding kappa P)) := by
  unfold Plucker6.IsKlein
  rw [kleinQ_toComplexPlucker, diracConeEmbedding_null]
  exact_mod_cast (rfl : (0 : ℝ) = 0)

/--
The verified corridor: frozen `Q44` slice, null Dirac embedding, and complex
Klein-cone readback.
-/
theorem zorn_conformal_six_cone_packet
    (kappa : ℝ) (P : PauliParavector) :
    (toPACSplit44 (diracConeEmbedding kappa P)).x1 = 0 ∧
    (toPACSplit44 (diracConeEmbedding kappa P)).x2 = 0 ∧
    Q44 (toPACSplit44 (diracConeEmbedding kappa P)) = 0 ∧
    Plucker6.IsKlein
      (toComplexPlucker (diracConeEmbedding kappa P)) := by
  exact ⟨rfl, rfl, diracConeEmbedding_PACSplit44_null kappa P,
    diracConeEmbedding_isKlein kappa P⟩

end InfoGeometry.Bridge.ZornConformalSixCone

end noncomputable section
