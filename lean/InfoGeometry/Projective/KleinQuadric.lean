import Mathlib.Tactic

/-!
# InfoGeometry.Projective.KleinQuadric

Concrete Plücker/Klein quadric layer.

The Klein quadric is the projective quadric in `P(Λ² R⁴)` defined by

  p₀₁ p₂₃ - p₀₂ p₁₃ + p₀₃ p₁₂ = 0.

It represents lines in projective 3-space via Plücker coordinates.

This file proves:

* homogeneous scaling of the Klein quadratic form;
* projective well-definedness of the quadric equation;
* polar incidence homogeneity;
* decomposable bivectors `u ∧ v` satisfy the Plücker relation.

No quotient construction.
No wrappers.
No `sorry`.
-/

namespace InfoGeometry.Projective.KleinQuadric

/-- A coordinate vector in `R⁴`. -/
structure Vec4 (R : Type*) where
  x0 : R
  x1 : R
  x2 : R
  x3 : R

/--
Plücker coordinates on `Λ² R⁴`.

Coordinates are ordered as:

  p01, p02, p03, p12, p13, p23.
-/
structure Plucker6 (R : Type*) where
  p01 : R
  p02 : R
  p03 : R
  p12 : R
  p13 : R
  p23 : R

@[ext]
theorem Plucker6.ext {R : Type*} {P Q : Plucker6 R}
    (h01 : P.p01 = Q.p01)
    (h02 : P.p02 = Q.p02)
    (h03 : P.p03 = Q.p03)
    (h12 : P.p12 = Q.p12)
    (h13 : P.p13 = Q.p13)
    (h23 : P.p23 = Q.p23) :
    P = Q := by
  cases P
  cases Q
  cases h01
  cases h02
  cases h03
  cases h12
  cases h13
  cases h23
  rfl

namespace Plucker6

variable {R : Type*} [CommRing R]

/--
The Klein quadratic form:

  Q(P) = p01 p23 - p02 p13 + p03 p12.
-/
def kleinQ (P : Plucker6 R) : R :=
  P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12

/-- The affine cone over the Klein quadric. -/
def IsKlein (P : Plucker6 R) : Prop :=
  kleinQ P = 0

/-- Scalar multiplication of Plücker coordinates. -/
def scale (l : R) (P : Plucker6 R) : Plucker6 R where
  p01 := l * P.p01
  p02 := l * P.p02
  p03 := l * P.p03
  p12 := l * P.p12
  p13 := l * P.p13
  p23 := l * P.p23

/-- Coordinatewise addition of Plücker coordinates. -/
def add (P Q : Plucker6 R) : Plucker6 R where
  p01 := P.p01 + Q.p01
  p02 := P.p02 + Q.p02
  p03 := P.p03 + Q.p03
  p12 := P.p12 + Q.p12
  p13 := P.p13 + Q.p13
  p23 := P.p23 + Q.p23

/--
Quadratic homogeneity of the Klein form.

  Q(λP) = λ² Q(P).
-/
theorem kleinQ_scale (l : R) (P : Plucker6 R) :
    kleinQ (scale l P) = l ^ 2 * kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  unfold kleinQ scale
  ring

/--
The Klein quadric equation is preserved by arbitrary scalar scaling.
-/
theorem isKlein_scale_of
    (l : R) (P : Plucker6 R)
    (hP : IsKlein P) :
    IsKlein (scale l P) := by
  unfold IsKlein at *
  rw [kleinQ_scale l P, hP]
  ring

/--
For nonzero scalars over a ring with no zero divisors, the Klein equation is
equivalent after scaling.
-/
theorem isKlein_scale_iff
    [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0)
    (P : Plucker6 R) :
    IsKlein (scale l P) ↔ IsKlein P := by
  constructor
  · intro h
    unfold IsKlein at *
    rw [kleinQ_scale l P] at h
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
    exact (mul_eq_zero.mp h).resolve_left hl2
  · intro h
    exact isKlein_scale_of l P h

/--
The polar form associated to the Klein quadratic form:

  B(P,Q) = Q(P+Q) - Q(P) - Q(Q).
-/
def polar (P Q : Plucker6 R) : R :=
  kleinQ (add P Q) - kleinQ P - kleinQ Q

/--
Expanded coordinate formula for the Klein polar form.
-/
theorem polar_formula (P Q : Plucker6 R) :
    polar P Q =
      P.p01 * Q.p23 + Q.p01 * P.p23
      - (P.p02 * Q.p13 + Q.p02 * P.p13)
      + (P.p03 * Q.p12 + Q.p03 * P.p12) := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold polar kleinQ add
  ring

/--
Left homogeneity of the Klein polar form.
-/
theorem polar_scale_left (l : R) (P Q : Plucker6 R) :
    polar (scale l P) Q = l * polar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold polar kleinQ add scale
  ring

/--
Right homogeneity of the Klein polar form.
-/
theorem polar_scale_right (l : R) (P Q : Plucker6 R) :
    polar P (scale l Q) = l * polar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold polar kleinQ add scale
  ring

/--
Polar incidence associated to the Klein quadric.
-/
def Incident (P Q : Plucker6 R) : Prop :=
  polar P Q = 0

/--
Left projective scaling preserves and reflects Klein polar incidence.
-/
theorem incident_scale_left_iff
    [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0)
    (P Q : Plucker6 R) :
    Incident (scale l P) Q ↔ Incident P Q := by
  unfold Incident
  rw [polar_scale_left l P Q]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hl
  · intro h
    rw [h, mul_zero]

/--
Right projective scaling preserves and reflects Klein polar incidence.
-/
theorem incident_scale_right_iff
    [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0)
    (P Q : Plucker6 R) :
    Incident P (scale l Q) ↔ Incident P Q := by
  unfold Incident
  rw [polar_scale_right l P Q]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hl
  · intro h
    rw [h, mul_zero]

/--
Independent projective scaling preserves and reflects Klein polar incidence.
-/
theorem incident_scale_iff
    [NoZeroDivisors R]
    (l m : R) (hl : l ≠ 0) (hm : m ≠ 0)
    (P Q : Plucker6 R) :
    Incident (scale l P) (scale m Q) ↔ Incident P Q := by
  calc
    Incident (scale l P) (scale m Q)
        ↔ Incident P (scale m Q) :=
          incident_scale_left_iff l hl P (scale m Q)
    _   ↔ Incident P Q :=
          incident_scale_right_iff m hm P Q

end Plucker6

namespace Vec4

variable {R : Type*} [CommRing R]

/--
Plücker coordinates of the decomposable bivector `u ∧ v`.
-/
def wedge (u v : Vec4 R) : Plucker6 R where
  p01 := u.x0 * v.x1 - u.x1 * v.x0
  p02 := u.x0 * v.x2 - u.x2 * v.x0
  p03 := u.x0 * v.x3 - u.x3 * v.x0
  p12 := u.x1 * v.x2 - u.x2 * v.x1
  p13 := u.x1 * v.x3 - u.x3 * v.x1
  p23 := u.x2 * v.x3 - u.x3 * v.x2

/--
The Plücker relation.

Every decomposable bivector `u ∧ v` lies on the Klein quadric.
-/
theorem wedge_isKlein (u v : Vec4 R) :
    Plucker6.IsKlein (wedge u v) := by
  rcases u with ⟨u0, u1, u2, u3⟩
  rcases v with ⟨v0, v1, v2, v3⟩
  unfold wedge Plucker6.IsKlein Plucker6.kleinQ
  ring

/--
Swapping the two spanning vectors negates the Plücker point.
-/
theorem wedge_swap (u v : Vec4 R) :
    wedge v u = Plucker6.scale (-1 : R) (wedge u v) := by
  rcases u with ⟨u0, u1, u2, u3⟩
  rcases v with ⟨v0, v1, v2, v3⟩
  ext <;> unfold wedge Plucker6.scale <;> ring

end Vec4

end InfoGeometry.Projective.KleinQuadric
