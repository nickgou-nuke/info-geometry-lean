/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra

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

section Ring

variable {R : Type*} [Ring R]

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
  noncomm_ring

/--
Euler homogeneous contraction for the Klein quadric:
  B(P,P) = 2 Q(P).
-/
theorem polar_self (P : Plucker6 R) :
    polar P P = 2 * kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  simp [polar, kleinQ, add]
  noncomm_ring

/--
Polar incidence associated to the Klein quadric.
-/
def Incident (P Q : Plucker6 R) : Prop :=
  polar P Q = 0

end Ring

section CentralScalar

variable {R : Type*} [Ring R]

/-- A central scalar moves past any coordinate product. -/
theorem central_mul_left {l : R} (hl : ∀ c : R, l * c = c * l) (c d : R) :
    c * (l * d) = l * (c * d) := by
  rw [← mul_assoc, ← hl c, mul_assoc]

/-- Left homogeneity of the polar form for a central scalar in an operator ring. -/
theorem polar_scale_left_of_central {l : R} (hl : ∀ c : R, l * c = c * l) (P Q : Plucker6 R) :
    polar (scale l P) Q = l * polar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  have hc := central_mul_left hl
  simp only [polar, kleinQ, add, scale, mul_add, add_mul, mul_sub, mul_assoc, hc]
  noncomm_ring

/-- Right homogeneity of the polar form for a central scalar in an operator ring. -/
theorem polar_scale_right_of_central {l : R} (hl : ∀ c : R, l * c = c * l) (P Q : Plucker6 R) :
    polar P (scale l Q) = l * polar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  have hc := central_mul_left hl
  simp only [polar, kleinQ, add, scale, mul_add, add_mul, mul_sub, mul_assoc, hc]
  noncomm_ring

/-- Quadratic homogeneity `Q(λP) = λ² Q(P)` for a central scalar in an operator ring. -/
theorem kleinQ_scale_of_central {l : R} (hl : ∀ c : R, l * c = c * l) (P : Plucker6 R) :
    kleinQ (scale l P) = l ^ 2 * kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  have hc := central_mul_left hl
  simp only [kleinQ, scale, mul_add, mul_sub, mul_assoc, hc]
  noncomm_ring

/-- The operator Klein quadric is stable under central scaling. -/
theorem isKlein_scale_of_central {l : R} (hl : ∀ c : R, l * c = c * l) (P : Plucker6 R)
    (hP : IsKlein P) : IsKlein (scale l P) := by
  unfold IsKlein at *
  rw [kleinQ_scale_of_central hl P, hP, mul_zero]

end CentralScalar

section CommRing

variable {R : Type*} [CommRing R]

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
Right homogeneity of the Klein polar form.
-/
theorem polar_scale_right (l : R) (P Q : Plucker6 R) :
    polar P (scale l Q) = l * polar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold polar kleinQ add scale
  ring

/--
Directional expansion of the Klein quadric:
  Q(P + τX) = Q(P) + τ B(P,X) + τ² Q(X).
-/
theorem kleinQ_add_scale (τ : R) (P X : Plucker6 R) :
    kleinQ (add P (scale τ X)) = kleinQ P + τ * polar P X + τ ^ 2 * kleinQ X := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases X with ⟨x01, x02, x03, x12, x13, x23⟩
  simp [kleinQ, add, scale, polar]
  ring

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

end CommRing

end Plucker6

namespace Vec4

section Ring

variable {R : Type*} [Ring R]

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

end Ring

section CommRing

variable {R : Type*} [CommRing R]

/--
Swapping the two spanning vectors negates the Plücker point.
-/
theorem wedge_swap (u v : Vec4 R) :
    wedge v u = Plucker6.scale (-1 : R) (wedge u v) := by
  rcases u with ⟨u0, u1, u2, u3⟩
  rcases v with ⟨v0, v1, v2, v3⟩
  ext <;> unfold wedge Plucker6.scale <;> ring

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

end CommRing

section Field

variable {K : Type*} [Field K]

/-- On the affine chart `p01 ≠ 0`, the Klein relation is sufficient for a
Plücker vector to be represented by an actual wedge. The explicit factors
are `u = (1, 0, -p12/p01, -p13/p01)` and
`v = (0, p01, p02, p03)`. This is a chart-level converse; it makes no claim
about points outside this pivot chart. -/
theorem exists_wedge_eq_of_isKlein_of_p01_ne_zero (P : Plucker6 K)
    (hp : P.p01 ≠ 0) (hP : Plucker6.IsKlein P) :
    ∃ u v : Vec4 K, Vec4.wedge u v = P := by
  change P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12 = 0 at hP
  let u : Vec4 K := ⟨1, 0, -P.p12 / P.p01, -P.p13 / P.p01⟩
  let v : Vec4 K := ⟨0, P.p01, P.p02, P.p03⟩
  refine ⟨u, v, ?_⟩
  apply Plucker6.ext
  · simp [Vec4.wedge, u, v]
  · simp [Vec4.wedge, u, v]
  · simp [Vec4.wedge, u, v]
  · simp [Vec4.wedge, u, v]
    field_simp [hp]
  · simp [Vec4.wedge, u, v]
    field_simp [hp]
  · simp [Vec4.wedge, u, v]
    field_simp [hp]
    linear_combination -hP

end Field

end Vec4

end InfoGeometry.Projective.KleinQuadric
