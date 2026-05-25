import Mathlib.Tactic

/-!
# Concrete Zorn composition and logarithmic volume cocycle

This file proves the split-octonion/Zorn determinant composition law in
coordinates, then derives the logarithmic volume-change cocycle.

No wrappers. No abstract datum. No `sorry`.
-/

namespace InfoGeometry.Algebra.Zorn.Concrete

/--
A concrete Zorn cell

  [ r   x ]
  [ y   s ]

with `x = (x1,x2,x3)` and `y = (y1,y2,y3)`.
-/
structure ZornCell (R : Type*) where
  r : R
  s : R
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

/-- Coordinate composition identity for `mulZ`. -/
theorem detZ_mulZ (X Y : ZornCell R) :
    detZ (mulZ X Y) = detZ X * detZ Y := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  rcases Y with ⟨r₂, s₂, u1, u2, u3, v1, v2, v3⟩
  unfold detZ mulZ
  simp
  ring

/--
Zorn Composition Theorem:

`detZ (X * Y) = detZ X * detZ Y`.
-/
theorem detZ_mul (X Y : ZornCell R) :
    detZ (X * Y) = detZ X * detZ Y := by
  simpa [instMulZornCell] using detZ_mulZ X Y

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

/-- Left null factor forces the product to be Zorn-null. -/
theorem detZ_mul_eq_zero_of_left_null
    (X Y : ZornCell R)
    (hX : detZ X = 0) :
    detZ (X * Y) = 0 := by
  rw [detZ_mul, hX, zero_mul]

/-- Right null factor forces the product to be Zorn-null. -/
theorem detZ_mul_eq_zero_of_right_null
    (X Y : ZornCell R)
    (hY : detZ Y = 0) :
    detZ (X * Y) = 0 := by
  rw [detZ_mul, hY, mul_zero]

/--
Negative logarithmic determinant potential, abstracted over any additive
logarithm-like map.
-/
def negLogDet
    {A : Type*} [AddCommGroup A]
    (ell : R → A)
    (X : ZornCell R) : A :=
  -ell (detZ X)

/--
The negative log-determinant is an additive cocycle under Zorn multiplication.
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

end InfoGeometry.Algebra.Zorn.Concrete
