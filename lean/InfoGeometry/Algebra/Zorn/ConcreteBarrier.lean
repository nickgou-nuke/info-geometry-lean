import Mathlib

/-!
# InfoGeometry.Algebra.Zorn.ConcreteBarrier

Concrete Zorn determinant composition and logarithmic barrier lemmas.

This file proves:

* the coordinate Zorn composition theorem;
* null preservation under Zorn multiplication;
* norm-one determinant preservation;
* the negative-log determinant cocycle;
* the diagonal-slice logarithmic barrier identity;
* first and second derivative formulas for the diagonal barrier.

No wrappers.
No `sorry`.
No self-concordance claim.
No global analytic boundary-divergence claim.
-/

noncomputable section

namespace ConcreteBarrier

/-!
## 1. Concrete 8D Zorn cell
-/

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

/--
Correct Zorn product.

The sign convention is:

  top-right     = r u + d x - y × v
  bottom-left   = c y + s v + x × u

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
The concrete Zorn composition theorem:

`detZ (X * Y) = detZ X * detZ Y`.

This is the split-octonion composition norm identity, proved by coordinate
polynomial calculation.
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
Negative logarithmic determinant potential, abstracted over an additive
logarithm-like map.

For analytic use, `ell` may later be instantiated as `log |·|` on a
nonzero/positive domain. Here we only need the algebraic law

`ell (a * b) = ell a + ell b`.
-/
def negLogDet
    {A : Type*} [AddCommGroup A]
    (ell : R → A)
    (X : ZornCell R) : A :=
  - ell (detZ X)

/--
The negative log-determinant is an additive cocycle under Zorn multiplication.

If `ell` sends multiplication to addition, then

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


/-!
## 2. Diagonal positive Zorn slice and logarithmic barrier
-/

/--
Diagonal Zorn slice

  [ a   0 ]
  [ 0   b ]

with determinant `a * b`.
-/
structure ZornSlice where
  a : ℝ
  b : ℝ

namespace ZornSlice

/-- Diagonal determinant. -/
def det (X : ZornSlice) : ℝ :=
  X.a * X.b

/-- Positive diagonal cone. -/
def InCone (X : ZornSlice) : Prop :=
  0 < X.a ∧ 0 < X.b

/-- Boundary/null condition on the diagonal slice. -/
def IsBoundary (X : ZornSlice) : Prop :=
  X.det = 0

/-- Product on the diagonal slice. -/
def mulZ (X Y : ZornSlice) : ZornSlice where
  a := X.a * Y.a
  b := X.b * Y.b

instance instMulZornSlice : Mul ZornSlice where
  mul := mulZ

/-- Determinant is multiplicative on the diagonal slice. -/
@[simp] theorem det_mul (X Y : ZornSlice) :
    det (X * Y) = det X * det Y := by
  change det (mulZ X Y) = det X * det Y
  simp [det, mulZ]
  ring_nf

/-- A point in the positive cone has positive determinant. -/
theorem det_pos_of_inCone
    (X : ZornSlice)
    (hX : X.InCone) :
    0 < X.det := by
  exact mul_pos hX.1 hX.2

/-- A point in the positive cone is not on the boundary. -/
theorem not_boundary_of_inCone
    (X : ZornSlice)
    (hX : X.InCone) :
    ¬ X.IsBoundary := by
  intro hB
  have hpos : 0 < X.det := det_pos_of_inCone X hX
  unfold IsBoundary at hB
  linarith

/-- The positive cone is closed under diagonal multiplication. -/
theorem inCone_mul
    (X Y : ZornSlice)
    (hX : X.InCone)
    (hY : Y.InCone) :
    (X * Y).InCone := by
  constructor
  · exact mul_pos hX.1 hY.1
  · exact mul_pos hX.2 hY.2

/--
Diagonal logarithmic barrier

`F(a,b) = -log a - log b`.
-/
def barrier (X : ZornSlice) : ℝ :=
  - Real.log X.a - Real.log X.b

/--
On the positive cone, the diagonal barrier is the negative log determinant:

`F(X) = -log(det X)`.
-/
theorem barrier_eq_neg_log_det
    (X : ZornSlice)
    (hX : X.InCone) :
    barrier X = - Real.log X.det := by
  unfold barrier det
  rw [Real.log_mul hX.1.ne' hX.2.ne']
  ring

/--
The diagonal barrier is additive under diagonal multiplication inside the
positive cone.

This is the concrete logarithmic volume-change cocycle:

`F(X * Y) = F(X) + F(Y)`.
-/
theorem barrier_mul
    (X Y : ZornSlice)
    (hX : X.InCone)
    (hY : Y.InCone) :
    barrier (X * Y) = barrier X + barrier Y := by
  have hXY : (X * Y).InCone := inCone_mul X Y hX hY
  rw [barrier_eq_neg_log_det (X * Y) hXY]
  rw [barrier_eq_neg_log_det X hX]
  rw [barrier_eq_neg_log_det Y hY]
  rw [det_mul]
  have hdetX : (det X) ≠ 0 := (det_pos_of_inCone X hX).ne'
  have hdetY : (det Y) ≠ 0 := (det_pos_of_inCone Y hY).ne'
  rw [Real.log_mul hdetX hdetY]
  ring

/--
First derivative in the `a` coordinate:

`d/da (-log a - log b) = -1/a`.
-/
theorem barrier_deriv_a
    (a b : ℝ)
    (ha : a ≠ 0) :
    HasDerivAt
      (fun x : ℝ => - Real.log x - Real.log b)
      (-(1 / a))
      a := by
  have h1 : HasDerivAt (fun x : ℝ => -(Real.log x)) (-(1 / a)) a := by
    simpa [one_div] using (Real.hasDerivAt_log ha).neg
  have h2 : HasDerivAt (fun _ : ℝ => -Real.log b) 0 a := by
    simpa using hasDerivAt_const a (-Real.log b)
  change HasDerivAt ((fun x : ℝ => -Real.log x) + fun _ : ℝ => -Real.log b) (-(1 / a)) a
  simpa using h1.add h2

/--
First derivative in the `b` coordinate:

`d/db (-log a - log b) = -1/b`.
-/
theorem barrier_deriv_b
    (a b : ℝ)
    (hb : b ≠ 0) :
    HasDerivAt
      (fun y : ℝ => - Real.log a - Real.log y)
      (-(1 / b))
      b := by
  have h1 : HasDerivAt (fun _ : ℝ => -Real.log a) 0 b := by
    simpa using hasDerivAt_const b (-Real.log a)
  have h2 : HasDerivAt (fun y : ℝ => -(Real.log y)) (-(1 / b)) b := by
    simpa [one_div] using (Real.hasDerivAt_log hb).neg
  change HasDerivAt ((fun _ : ℝ => -Real.log a) + fun y : ℝ => -Real.log y) (-(1 / b)) b
  simpa [add_comm] using h1.add h2

/--
Second derivative in the `a` coordinate:

`d/da (-1/a) = 1/a²`.
-/
theorem barrier_hessian_a
    (a : ℝ)
    (ha : a ≠ 0) :
    HasDerivAt
      (fun x : ℝ => -(1 / x))
      (1 / (a ^ 2))
      a := by
  have h :
      HasDerivAt
        (fun x : ℝ => - x⁻¹)
        (a⁻¹ ^ 2)
        a := by
    simpa using (hasDerivAt_inv ha).neg
  have hder : a⁻¹ ^ 2 = 1 / (a ^ 2) := by
    field_simp [ha]
  simpa [one_div, hder] using h

/--
Second derivative in the `b` coordinate:

`d/db (-1/b) = 1/b²`.
-/
theorem barrier_hessian_b
    (b : ℝ)
    (hb : b ≠ 0) :
    HasDerivAt
      (fun y : ℝ => -(1 / y))
      (1 / (b ^ 2))
      b := by
  have h :
      HasDerivAt
        (fun y : ℝ => - y⁻¹)
        (b⁻¹ ^ 2)
        b := by
    simpa using (hasDerivAt_inv hb).neg
  have hder : b⁻¹ ^ 2 = 1 / (b ^ 2) := by
    field_simp [hb]
  simpa [one_div, hder] using h

/-- The `a` Hessian entry is positive inside the positive cone. -/
theorem barrier_hessian_a_pos
    (a : ℝ)
    (ha : 0 < a) :
    0 < 1 / (a ^ 2) := by
  positivity

/-- The `b` Hessian entry is positive inside the positive cone. -/
theorem barrier_hessian_b_pos
    (b : ℝ)
    (hb : 0 < b) :
    0 < 1 / (b ^ 2) := by
  positivity

end ZornSlice

end ConcreteBarrier
