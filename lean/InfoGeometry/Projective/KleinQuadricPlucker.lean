import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Projective.KleinQuadricPlucker

Concrete Klein quadric theorem.

This file proves the coordinate Plucker relation for lines in projective
3-space:

  p01 p23 - p02 p13 + p03 p12 = 0.

It also proves the scaling law for the Klein quadratic equation and the
polarization identity for the associated quadric.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Projective.KleinQuadricPlucker

/-- Homogeneous coordinates in a 4-dimensional vector space. -/
structure Vec4 (R : Type*) where
  x0 : R
  x1 : R
  x2 : R
  x3 : R

/-- Plucker coordinates on `Λ² R⁴`, ordered as `01,02,03,12,13,23`. -/
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

namespace Vec4

variable {R : Type*} [CommRing R]

/-- Scalar multiplication of homogeneous coordinates. -/
def scale (l : R) (X : Vec4 R) : Vec4 R where
  x0 := l * X.x0
  x1 := l * X.x1
  x2 := l * X.x2
  x3 := l * X.x3

end Vec4

namespace Plucker6

variable {R : Type*} [CommRing R]

/-- Coordinatewise addition of Plucker coordinate vectors. -/
def add (P Q : Plucker6 R) : Plucker6 R where
  p01 := P.p01 + Q.p01
  p02 := P.p02 + Q.p02
  p03 := P.p03 + Q.p03
  p12 := P.p12 + Q.p12
  p13 := P.p13 + Q.p13
  p23 := P.p23 + Q.p23

/-- Scalar multiplication of Plucker coordinates. -/
def scale (l : R) (P : Plucker6 R) : Plucker6 R where
  p01 := l * P.p01
  p02 := l * P.p02
  p03 := l * P.p03
  p12 := l * P.p12
  p13 := l * P.p13
  p23 := l * P.p23

/--
The Klein quadric equation in Plucker coordinates:

`p01 p23 - p02 p13 + p03 p12`.
-/
def kleinQ (P : Plucker6 R) : R :=
  P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12

/--
The polar bilinear form associated to the Klein quadric.

It is the cross term in

`kleinQ (P + Q) = kleinQ P + kleinQ Q + kleinPolar P Q`.
-/
def kleinPolar (P Q : Plucker6 R) : R :=
  P.p01 * Q.p23 + Q.p01 * P.p23
    - (P.p02 * Q.p13 + Q.p02 * P.p13)
    + (P.p03 * Q.p12 + Q.p03 * P.p12)

/--
Plucker coordinates of the line spanned by two homogeneous vectors `X,Y`.

These are the `2 × 2` minors `xᵢ yⱼ - xⱼ yᵢ`.
-/
def pluckerLine (X Y : Vec4 R) : Plucker6 R where
  p01 := X.x0 * Y.x1 - X.x1 * Y.x0
  p02 := X.x0 * Y.x2 - X.x2 * Y.x0
  p03 := X.x0 * Y.x3 - X.x3 * Y.x0
  p12 := X.x1 * Y.x2 - X.x2 * Y.x1
  p13 := X.x1 * Y.x3 - X.x3 * Y.x1
  p23 := X.x2 * Y.x3 - X.x3 * Y.x2

/--
The Klein quadric / Plucker relation.

Every decomposable bivector `X ∧ Y`, written in Plucker coordinates, lies on
the Klein quadric.
-/
theorem kleinQ_pluckerLine (X Y : Vec4 R) :
    kleinQ (pluckerLine X Y) = 0 := by
  rcases X with ⟨x0, x1, x2, x3⟩
  rcases Y with ⟨y0, y1, y2, y3⟩
  unfold kleinQ pluckerLine
  ring

/-- Scaling the first spanning vector scales all Plucker coordinates. -/
theorem pluckerLine_scale_left
    (l : R) (X Y : Vec4 R) :
    pluckerLine (Vec4.scale l X) Y =
      scale l (pluckerLine X Y) := by
  rcases X with ⟨x0, x1, x2, x3⟩
  rcases Y with ⟨y0, y1, y2, y3⟩
  apply Plucker6.ext <;> unfold pluckerLine Vec4.scale scale <;> ring

/-- Scaling the second spanning vector scales all Plucker coordinates. -/
theorem pluckerLine_scale_right
    (m : R) (X Y : Vec4 R) :
    pluckerLine X (Vec4.scale m Y) =
      scale m (pluckerLine X Y) := by
  rcases X with ⟨x0, x1, x2, x3⟩
  rcases Y with ⟨y0, y1, y2, y3⟩
  apply Plucker6.ext <;> unfold pluckerLine Vec4.scale scale <;> ring

/-- Scaling Plucker coordinates scales the Klein quadratic form by `l²`. -/
theorem kleinQ_scale
    (l : R) (P : Plucker6 R) :
    kleinQ (scale l P) = l ^ 2 * kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  unfold kleinQ scale
  ring

/--
The Klein quadric condition is projectively well-defined.

Scaling by a nonzero scalar does not change whether a Plucker vector lies on
the Klein quadric.
-/
theorem kleinQ_scale_zero_iff
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (l : R) (hl : l ≠ 0) (P : Plucker6 R) :
    kleinQ (scale l P) = 0 ↔ kleinQ P = 0 := by
  constructor
  · intro h
    rw [kleinQ_scale] at h
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
    rcases mul_eq_zero.mp h with hzero | hq
    · exact False.elim (hl2 hzero)
    · exact hq
  · intro h
    rw [kleinQ_scale, h, mul_zero]

/-- Polarization identity for the Klein quadratic form. -/
theorem kleinQ_add
    (P Q : Plucker6 R) :
    kleinQ (add P Q) =
      kleinQ P + kleinQ Q + kleinPolar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold kleinQ kleinPolar add
  ring

/-- The Klein polar form is homogeneous in the left argument. -/
theorem kleinPolar_scale_left
    (l : R) (P Q : Plucker6 R) :
    kleinPolar (scale l P) Q = l * kleinPolar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold kleinPolar scale
  ring

/-- The Klein polar form is homogeneous in the right argument. -/
theorem kleinPolar_scale_right
    (m : R) (P Q : Plucker6 R) :
    kleinPolar P (scale m Q) = m * kleinPolar P Q := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold kleinPolar scale
  ring

/--
The Klein polar form is symmetric.

This is the bilinear form associated to the Klein quadratic equation.
-/
theorem kleinPolar_comm
    (P Q : Plucker6 R) :
    kleinPolar P Q = kleinPolar Q P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  unfold kleinPolar
  ring

/--
The Klein polar form is additive in the left argument.
-/
theorem kleinPolar_add_left
    (P Q R₀ : Plucker6 R) :
    kleinPolar (add P Q) R₀ =
      kleinPolar P R₀ + kleinPolar Q R₀ := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  rcases Q with ⟨q01, q02, q03, q12, q13, q23⟩
  rcases R₀ with ⟨r01, r02, r03, r12, r13, r23⟩
  unfold kleinPolar add
  ring

/--
The Klein polar form is additive in the right argument.
-/
theorem kleinPolar_add_right
    (P Q R₀ : Plucker6 R) :
    kleinPolar P (add Q R₀) =
      kleinPolar P Q + kleinPolar P R₀ := by
  rw [kleinPolar_comm P (add Q R₀)]
  rw [kleinPolar_add_left Q R₀ P]
  rw [kleinPolar_comm Q P]
  rw [kleinPolar_comm R₀ P]

/--
The Klein polar form is exactly the cross-term of the Klein quadratic form:

`B(P,Q) = Q(P+Q) - Q(P) - Q(Q)`.
-/
theorem kleinPolar_eq_kleinQ_add_sub
    (P Q : Plucker6 R) :
    kleinPolar P Q =
      kleinQ (add P Q) - kleinQ P - kleinQ Q := by
  rw [kleinQ_add]
  ring

/--
The Klein polar form is the polarization of the Klein quadratic form.

In particular,

  `kleinPolar P P = 2 * kleinQ P`.
-/
theorem kleinPolar_self
    {R : Type*} [CommRing R]
    (P : Plucker6 R) :
    kleinPolar P P = 2 * kleinQ P := by
  rcases P with ⟨p01, p02, p03, p12, p13, p23⟩
  unfold kleinPolar kleinQ
  ring

/--
A point on the Klein quadric is self-orthogonal for the associated polar form.
-/
theorem kleinPolar_self_of_kleinQ_zero
    {R : Type*} [CommRing R]
    (P : Plucker6 R)
    (hP : kleinQ P = 0) :
    kleinPolar P P = 0 := by
  rw [kleinPolar_self, hP]
  ring

/--
Conversely, if `2 ≠ 0` and the ring has no zero divisors, self-orthogonality
for the polar form implies the Klein quadratic equation.
-/
theorem kleinQ_zero_of_kleinPolar_self_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0)
    (P : Plucker6 R)
    (hP : kleinPolar P P = 0) :
    kleinQ P = 0 := by
  rw [kleinPolar_self] at hP
  rcases mul_eq_zero.mp hP with htwo | hQ
  · exact False.elim (h2 htwo)
  · exact hQ

/--
Over a ring with no zero divisors and `2 ≠ 0`, the Klein quadric equation is
equivalent to self-orthogonality for the associated polar bilinear form.
-/
theorem kleinPolar_self_zero_iff_kleinQ_zero_of_two_ne_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0)
    (P : Plucker6 R) :
    kleinPolar P P = 0 ↔ kleinQ P = 0 := by
  constructor
  · exact kleinQ_zero_of_kleinPolar_self_zero h2 P
  · exact kleinPolar_self_of_kleinQ_zero P

/--
Projective well-definedness of Klein-polar incidence.

For nonzero scalars `l, m`, the polar incidence equation

`kleinPolar P Q = 0`

is invariant under independent projective rescalings of `P` and `Q`.
-/
theorem kleinPolar_projective_incidence
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (l m : R) (hl : l ≠ 0) (hm : m ≠ 0)
    (P Q : Plucker6 R) :
    kleinPolar P Q = 0 ↔
      kleinPolar (scale l P) (scale m Q) = 0 := by
  constructor
  · intro h
    rw [kleinPolar_scale_left, kleinPolar_scale_right, h]
    ring
  · intro h
    rw [kleinPolar_scale_left, kleinPolar_scale_right] at h
    have hInner : m * kleinPolar P Q = 0 := by
      rcases mul_eq_zero.mp h with hlzero | hrest
      · exact False.elim (hl hlzero)
      · exact hrest
    rcases mul_eq_zero.mp hInner with hmzero | hpolar
    · exact False.elim (hm hmzero)
    · exact hpolar

end Plucker6

/--
Local converse on the affine `p01 ≠ 0` chart over a field.

If the Klein relation holds and the `p01` coordinate is nonzero, then the
Plücker point is represented by an explicit decomposable line.
This is a chart theorem, not the global projective quotient converse.
-/
theorem kleinRel_exists_pluckerLine_of_p01_ne_zero
    [Field R]
    (P : Plucker6 R)
    (hK : Plucker6.kleinQ P = 0)
    (hp01 : P.p01 ≠ 0) :
    ∃ X Y : Vec4 R, Plucker6.pluckerLine X Y = P := by
  let X : Vec4 R :=
    { x0 := 1, x1 := 0, x2 := -(P.p12 / P.p01), x3 := -(P.p13 / P.p01) }
  let Y : Vec4 R :=
    { x0 := 0, x1 := P.p01, x2 := P.p02, x3 := P.p03 }
  refine ⟨X, Y, ?_⟩
  apply Plucker6.ext <;> dsimp [X, Y, Plucker6.pluckerLine]
  · ring_nf
  · ring_nf
  · ring_nf
  · field_simp [hp01]
    ring_nf
  · field_simp [hp01]
    ring_nf
  · have hK' : P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12 = 0 := by
      unfold Plucker6.kleinQ at hK
      exact hK
    have hmul : P.p01 * P.p23 = P.p02 * P.p13 - P.p03 * P.p12 := by
      have h' :=
        congrArg (fun t => t + P.p02 * P.p13 - P.p03 * P.p12) hK'
      ring_nf at h'
      exact h'
    field_simp [hp01]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using hmul.symm

/--
Local converse on the affine `p02 ≠ 0` chart over a field.

If the Klein relation holds and the `p02` coordinate is nonzero, then the
Plücker point is represented by an explicit decomposable line.
This is a chart theorem, not the global projective quotient converse.
-/
theorem kleinRel_exists_pluckerLine_of_p02_ne_zero
    [Field R]
    (P : Plucker6 R)
    (hK : Plucker6.kleinQ P = 0)
    (hp02 : P.p02 ≠ 0) :
    ∃ X Y : Vec4 R, Plucker6.pluckerLine X Y = P := by
  let X : Vec4 R :=
    { x0 := 1, x1 := P.p12 / P.p02, x2 := 0, x3 := -(P.p23 / P.p02) }
  let Y : Vec4 R :=
    { x0 := 0, x1 := P.p01, x2 := P.p02, x3 := P.p03 }
  refine ⟨X, Y, ?_⟩
  apply Plucker6.ext <;> dsimp [X, Y, Plucker6.pluckerLine]
  · ring_nf
  · ring_nf
  · ring_nf
  · field_simp [hp02]
    ring_nf
  · have hK' : P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12 = 0 := by
      unfold Plucker6.kleinQ at hK
      exact hK
    have hmul : P.p02 * P.p13 = P.p01 * P.p23 + P.p03 * P.p12 := by
      have h' := congrArg (fun t => t + P.p02 * P.p13) hK'
      ring_nf at h'
      exact h'.symm
    field_simp [hp02]
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hmul.symm
  · field_simp [hp02]
    ring_nf

/--
Local converse on the affine `p03 ≠ 0` chart over a field.

If the Klein relation holds and the `p03` coordinate is nonzero, then the
Plücker point is represented by an explicit decomposable line.
This is a chart theorem, not the global projective quotient converse.
-/
theorem kleinRel_exists_pluckerLine_of_p03_ne_zero
    [Field R]
    (P : Plucker6 R)
    (hK : Plucker6.kleinQ P = 0)
    (hp03 : P.p03 ≠ 0) :
    ∃ X Y : Vec4 R, Plucker6.pluckerLine X Y = P := by
  let X : Vec4 R :=
    { x0 := 1, x1 := P.p13 / P.p03, x2 := P.p23 / P.p03, x3 := 0 }
  let Y : Vec4 R :=
    { x0 := 0, x1 := P.p01, x2 := P.p02, x3 := P.p03 }
  refine ⟨X, Y, ?_⟩
  apply Plucker6.ext <;> dsimp [X, Y, Plucker6.pluckerLine]
  · ring_nf
  · ring_nf
  · ring_nf
  · have hK' : P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12 = 0 := by
      unfold Plucker6.kleinQ at hK
      exact hK
    have hmul : P.p03 * P.p12 = P.p02 * P.p13 - P.p01 * P.p23 := by
      have h' := congrArg (fun t => t + P.p02 * P.p13 - P.p01 * P.p23) hK'
      ring_nf at h'
      simpa [sub_eq_add_neg, add_comm] using h'
    field_simp [hp03]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using hmul.symm
  · field_simp [hp03]
    ring_nf
  · field_simp [hp03]
    ring_nf

end InfoGeometry.Projective.KleinQuadricPlucker
