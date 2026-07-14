import Mathlib.Tactic

/-!
# InfoGeometry.Algebra.Zorn.ConcreteComposition

Concrete coordinate proof of the Zorn determinant composition theorem.

This file proves:

* `detZ (X * Y) = detZ X * detZ Y`;
* null preservation under multiplication;
* norm-one determinant preservation;
* the negative-log determinant cocycle.

No wrappers. No `sorry`.
-/

namespace ConcreteComposition

/--
A concrete Zorn cell

  [ r   x ]
  [ y   s ]

with `x = (x1,x2,x3)` and `y = (y1,y2,y3)`.
-/
structure ZornCell (R : Type*) where
  r  : R
  s  : R
  x1 : R
  x2 : R
  x3 : R
  y1 : R
  y2 : R
  y3 : R

namespace ZornCell

variable {R : Type*} [CommRing R]

/-- Zorn determinant / split norm. -/
def detZ (X : ZornCell R) : R :=
  X.r * X.s - (X.x1 * X.y1 + X.x2 * X.y2 + X.x3 * X.y3)

/-! ## Zorn polar form: the bilinear form behind `Cl(4,4)` -/

/-- Coordinatewise addition of concrete Zorn cells. -/
def addZ (X Y : ZornCell R) : ZornCell R where
  r  := X.r  + Y.r
  s  := X.s  + Y.s
  x1 := X.x1 + Y.x1
  x2 := X.x2 + Y.x2
  x3 := X.x3 + Y.x3
  y1 := X.y1 + Y.y1
  y2 := X.y2 + Y.y2
  y3 := X.y3 + Y.y3

/--
The polar form of the Zorn determinant.

This is the bilinear form obtained from the quadratic form `detZ`:

`B_Z(X,Y) = detZ(X+Y) - detZ X - detZ Y`.

This is the form whose projective null cone is the Zorn quadric and whose
operatorization gives the associated split Clifford relation.
-/
def polarZ (X Y : ZornCell R) : R :=
  detZ (addZ X Y) - detZ X - detZ Y

/-- The Zorn polar form is symmetric. -/
theorem polarZ_comm (X Y : ZornCell R) :
    polarZ X Y = polarZ Y X := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r', s', x1', x2', x3', y1', y2', y3'⟩
  unfold polarZ addZ detZ
  ring

/--
Self-polarization identity for the Zorn determinant:

`B_Z(X,X) = 2 detZ(X)`.

This is the concrete bridge from the split-octonion/Zorn quadric to the
bilinear form behind the split Clifford algebra `Cl(4,4)`.
-/
theorem polarZ_self (X : ZornCell R) :
    polarZ X X = 2 * detZ X := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  unfold polarZ addZ detZ
  ring

/--
A Zorn-null vector is self-orthogonal for the polar form.
-/
theorem polarZ_self_of_detZ_zero
    (X : ZornCell R)
    (hX : detZ X = 0) :
    polarZ X X = 0 := by
  rw [polarZ_self, hX]
  ring

/--
Conversely, if `2 ≠ 0` and the base ring has no zero divisors, then
self-orthogonality for the polar form implies Zorn-nullness.
-/
theorem detZ_zero_of_polarZ_self_zero
    [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0)
    (X : ZornCell R)
    (hX : polarZ X X = 0) :
    detZ X = 0 := by
  rw [polarZ_self] at hX
  rcases mul_eq_zero.mp hX with htwo | hdet
  · exact False.elim (h2 htwo)
  · exact hdet

/--
Over a ring with no zero divisors and `2 ≠ 0`, the Zorn null equation is
equivalent to self-orthogonality for the associated polar bilinear form.
-/
theorem polarZ_self_zero_iff_detZ_zero_of_two_ne_zero
    [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0)
    (X : ZornCell R) :
    polarZ X X = 0 ↔ detZ X = 0 := by
  constructor
  · exact detZ_zero_of_polarZ_self_zero h2 X
  · exact polarZ_self_of_detZ_zero X

/--
Correct Zorn product.

The sign convention is:

  top-right    = r u + d x - y × v
  bottom-left  = c y + s v + x × u

With this convention, `detZ` is multiplicative.
-/
def mulZ (X Y : ZornCell R) : ZornCell R where
  r :=
    X.r * Y.r +
      (X.x1 * Y.y1 + X.x2 * Y.y2 + X.x3 * Y.y3)

  s :=
    (X.y1 * Y.x1 + X.y2 * Y.x2 + X.y3 * Y.x3) +
      X.s * Y.s

  x1 :=
    X.r * Y.x1 + Y.s * X.x1 -
      (X.y2 * Y.y3 - X.y3 * Y.y2)

  x2 :=
    X.r * Y.x2 + Y.s * X.x2 -
      (X.y3 * Y.y1 - X.y1 * Y.y3)

  x3 :=
    X.r * Y.x3 + Y.s * X.x3 -
      (X.y1 * Y.y2 - X.y2 * Y.y1)

  y1 :=
    Y.r * X.y1 + X.s * Y.y1 +
      (X.x2 * Y.x3 - X.x3 * Y.x2)

  y2 :=
    Y.r * X.y2 + X.s * Y.y2 +
      (X.x3 * Y.x1 - X.x1 * Y.x3)

  y3 :=
    Y.r * X.y3 + X.s * Y.y3 +
      (X.x1 * Y.x2 - X.x2 * Y.x1)

instance instMulZornCell : Mul (ZornCell R) where
  mul := mulZ

/--
Zorn Composition Theorem.

This is the split-octonion composition norm identity.
-/
theorem detZ_mul (X Y : ZornCell R) :
    detZ (X * Y) = detZ X * detZ Y := by
  change detZ (mulZ X Y) = detZ X * detZ Y
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r₂, s₂, u1, u2, u3, v1, v2, v3⟩
  unfold detZ mulZ
  ring_nf

/-- Left multiplication by a norm-one Zorn cell preserves `detZ`. -/
theorem detZ_left_mul_normOne
    (U X : ZornCell R)
    (hU : detZ U = 1) :
    detZ (U * X) = detZ X := by
  rw [detZ_mul, hU, one_mul]

/-- Right multiplication by a norm-one Zorn cell preserves `detZ`. -/
theorem detZ_right_mul_normOne
    (X U : ZornCell R)
    (hU : detZ U = 1) :
    detZ (X * U) = detZ X := by
  rw [detZ_mul, hU, mul_one]

/-- A left null factor forces the product to be Zorn-null. -/
theorem detZ_mul_eq_zero_of_left_null
    (X Y : ZornCell R)
    (hX : detZ X = 0) :
    detZ (X * Y) = 0 := by
  rw [detZ_mul, hX, zero_mul]

/-- A right null factor forces the product to be Zorn-null. -/
theorem detZ_mul_eq_zero_of_right_null
    (X Y : ZornCell R)
    (hY : detZ Y = 0) :
    detZ (X * Y) = 0 := by
  rw [detZ_mul, hY, mul_zero]

/--
Negative logarithmic determinant potential, abstracted over a logarithm-like
map.

For analytic use, `ell` can later be instantiated as `log |·|` on a valid
nonzero/positive domain. This theorem only needs the algebraic law

`ell (a * b) = ell a + ell b`.
-/
def negLogDet
    {A : Type*} [AddCommGroup A]
    (ell : R → A)
    (X : ZornCell R) : A :=
  - ell (detZ X)

/--
Negative-log determinant cocycle.

If `ell` converts multiplication into addition, then

`-ell(detZ (X * Y)) = -ell(detZ X) + -ell(detZ Y)`.
-/
theorem negLogDet_mul
    {A : Type*} [AddCommGroup A]
    (ell : R → A)
    (hlog_mul : ∀ a b : R, ell (a * b) = ell a + ell b)
    (X Y : ZornCell R) :
    negLogDet ell (X * Y) =
      negLogDet ell X + negLogDet ell Y := by
  unfold negLogDet
  rw [detZ_mul, hlog_mul]
  abel

end ZornCell

end ConcreteComposition
