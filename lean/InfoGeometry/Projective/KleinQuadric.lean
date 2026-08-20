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
The polar bilinear form associated to the Klein quadric:

  B(P, Q) = p01 q23 + q01 p23 - (p02 q13 + q02 p13) + (p03 q12 + q03 p12).
-/
def kleinPolar (P Q : Plucker6 R) : R :=
  P.p01 * Q.p23 + Q.p01 * P.p23 -
    (P.p02 * Q.p13 + Q.p02 * P.p13) +
    (P.p03 * Q.p12 + Q.p03 * P.p12)

/-- Klein polarization identity: Q(P + Q) = Q(P) + Q(Q) + B(P, Q). -/
theorem kleinQ_add (P Q : Plucker6 R) :
    kleinQ (add P Q) = kleinQ P + kleinQ Q + kleinPolar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold kleinQ add kleinPolar
  ring

/-- The polar bilinear form is symmetric. -/
theorem kleinPolar_comm (P Q : Plucker6 R) :
    kleinPolar P Q = kleinPolar Q P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold kleinPolar
  ring

/-- The diagonal of the polar form is `2 * Q(P)`. -/
theorem kleinPolar_self (P : Plucker6 R) :
    kleinPolar P P = 2 * kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  unfold kleinPolar kleinQ
  ring

/-- Polar incidence: two Plücker points are conjugate with respect to the quadric. -/
def Incident (P Q : Plucker6 R) : Prop :=
  kleinPolar P Q = 0

/-- Scaling Plücker coordinates scales the Klein quadratic form by `l²`. -/
theorem kleinQ_scale (l : R) (P : Plucker6 R) :
    kleinQ (scale l P) = l ^ 2 * kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  unfold kleinQ scale
  ring

/-- Scaling the first argument scales the polar form by `l`. -/
theorem kleinPolar_scale_left (l : R) (P Q : Plucker6 R) :
    kleinPolar (scale l P) Q = l * kleinPolar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold kleinPolar scale
  ring

/-- Scaling the second argument scales the polar form by `m`. -/
theorem kleinPolar_scale_right (m : R) (P Q : Plucker6 R) :
    kleinPolar P (scale m Q) = m * kleinPolar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold kleinPolar scale
  ring

/--
The Klein quadric condition is projectively well-defined.

Scaling by a nonzero scalar does not change whether a Plücker vector lies on the Klein quadric.
-/
theorem isKlein_scale_iff
    [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0) (P : Plucker6 R) :
    IsKlein (scale l P) ↔ IsKlein P := by
  unfold IsKlein
  rw [kleinQ_scale]
  constructor
  · intro h
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
    rcases mul_eq_zero.mp h with hzero | hq
    · exact False.elim (hl2 hzero)
    · exact hq
  · intro h
    rw [h, mul_zero]

/--
Projective scaling preserves and reflects Klein polar incidence.
-/
theorem incident_scale_iff
    [NoZeroDivisors R]
    (l m : R) (hl : l ≠ 0) (hm : m ≠ 0)
    (P Q : Plucker6 R) :
    Incident (scale l P) (scale m Q) ↔ Incident P Q := by
  unfold Incident
  rw [kleinPolar_scale_left, kleinPolar_scale_right]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hl0 | hrest
    · exact False.elim (hl hl0)
    · rcases mul_eq_zero.mp hrest with hm0 | hpolar
      · exact False.elim (hm hm0)
      · exact hpolar
  · intro h
    rw [h, mul_zero, mul_zero]

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

/-!
=============================================================================
Penrose Twistors & The Grassmannian Gr(2, 4) Embedding
=============================================================================
-/

/-- A Penrose twistor in homogeneous coordinates Z = (ω₀, ω₁, π₀, π₁). -/
abbrev Twistor (R : Type*) := Vec4 R

/-- Penrose Twistor Conjugation swapping chiral spinor components: C(ω, π) = (π, ω). -/
def twistorConjugation {R : Type*} (Z : Twistor R) : Twistor R where
  x0 := Z.x2
  x1 := Z.x3
  x2 := Z.x0
  x3 := Z.x1

/-- Twistor conjugation is an involution: C ∘ C = id. -/
@[simp] theorem twistorConjugation_involutive {R : Type*} (Z : Twistor R) :
    twistorConjugation (twistorConjugation Z) = Z := by
  cases Z
  rfl

/-- 
  THEOREM: Grassmannian Gr(2, 4) Lines are Null Rays on the Klein Quadric.
  For any two twistors Z₁, Z₂, their wedge product lies identically on the Klein Quadric.
-/
theorem gr24_twistor_line_on_klein_quadric {R : Type*} [CommRing R] (Z₁ Z₂ : Twistor R) :
    Plucker6.IsKlein (Vec4.wedge Z₁ Z₂) :=
  Vec4.wedge_isKlein Z₁ Z₂

end InfoGeometry.Projective.KleinQuadric
