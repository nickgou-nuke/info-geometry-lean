import Mathlib

/-!
# The supergraded relational split

The owner is deliberately formulated on homogeneous elements.  A function
assigning a parity to every element of a ring is not a grading, since sums of
different grades need not be homogeneous.  The `GradedRing` certificate below
therefore supplies homogeneous representatives and certified multiplication
of their grades, while leaving chirality and Clifford grade as separate data.
-/

namespace InfoGeometry.Canonical.SupergradedRelationalSplit

variable {A : Type*} [Ring A]

/-- A ring element together with its declared homogeneous parity. -/
structure Homogeneous (A : Type*) where
  value : A
  degree : Bool

/-- Certified multiplication of homogeneous representatives. -/
structure GradedRing (A : Type*) [Ring A] where
  mul : Homogeneous A → Homogeneous A → Homogeneous A
  mul_value : ∀ x y, (mul x y).value = x.value * y.value
  mul_degree : ∀ x y, (mul x y).degree = Bool.xor x.degree y.degree

/-- The Lie-super bracket of two homogeneous elements. -/
def superComm (x y : Homogeneous A) : A :=
  if x.degree && y.degree then
    x.value * y.value + y.value * x.value
  else
    x.value * y.value - y.value * x.value

/-- The graded-symmetric Jordan product of two homogeneous elements. -/
def superJordan (x y : Homogeneous A) (half : A) : A :=
  if x.degree && y.degree then
    half * (x.value * y.value - y.value * x.value)
  else
    half * (x.value * y.value + y.value * x.value)

/-- Multiplication in a certified graded ring has the summed parity. -/
theorem mul_mem_grade_add (G : GradedRing A) (x y : Homogeneous A) :
    (G.mul x y).degree = Bool.xor x.degree y.degree :=
  G.mul_degree x y

/-- The associative product is the sum of the two graded projections. -/
theorem mul_eq_superJordan_add_half_superComm
    (x y : Homogeneous A) (half : A) (h_half : half + half = 1) :
    x.value * y.value = superJordan x y half + half * superComm x y := by
  by_cases h : x.degree && y.degree
  · simp only [superJordan, superComm, h]
    calc
      x.value * y.value = (half + half) * (x.value * y.value) := by
        rw [h_half, one_mul]
      _ = half * (x.value * y.value) + half * (x.value * y.value) := by
        rw [add_mul]
      _ = half * (x.value * y.value - y.value * x.value) +
          half * (x.value * y.value + y.value * x.value) := by
        noncomm_ring
  · simp only [superJordan, superComm, h]
    calc
      x.value * y.value = (half + half) * (x.value * y.value) := by
        rw [h_half, one_mul]
      _ = half * (x.value * y.value) + half * (x.value * y.value) := by
        rw [add_mul]
      _ = half * (x.value * y.value + y.value * x.value) +
          half * (x.value * y.value - y.value * x.value) := by
        noncomm_ring

/-- Odd--odd super-Lie bracket is the ordinary anticommutator. -/
theorem superComm_odd_odd
    (x y : Homogeneous A)
    (hx : x.degree = true) (hy : y.degree = true) :
    superComm x y = x.value * y.value + y.value * x.value := by
  simp [superComm, hx, hy]

/-- Twice the odd--odd super-Jordan product is the ordinary commutator. -/
theorem two_superJordan_odd_odd
    (x y : Homogeneous A) (half : A)
    (h_half : half + half = 1)
    (hx : x.degree = true) (hy : y.degree = true) :
    superJordan x y half + superJordan x y half =
      x.value * y.value - y.value * x.value := by
  simp only [superJordan, hx, hy, Bool.true_and, ↓reduceIte]
  calc
    half * (x.value * y.value - y.value * x.value) +
        half * (x.value * y.value - y.value * x.value) =
      (half + half) * (x.value * y.value - y.value * x.value) := by
        rw [add_mul]
    _ = x.value * y.value - y.value * x.value := by
      rw [h_half, one_mul]

/-- Odd multiplication lands in the even grade of a certified graded ring. -/
theorem odd_mul_odd_mem_even
    (G : GradedRing A) (x y : Homogeneous A)
    (hx : x.degree = true) (hy : y.degree = true) :
    (G.mul x y).degree = false := by
  rw [G.mul_degree, hx, hy]
  rfl

/-- The chiral product readout exposes sum and difference projections. -/
theorem chiral_product_split
    (x y pplus pminus : Homogeneous A) (half : A)
    (hplus : x.value * y.value = pplus.value)
    (hminus : y.value * x.value = pminus.value)
    (hx : x.degree = true) (hy : y.degree = true) :
    superComm x y = pplus.value + pminus.value ∧
      superJordan x y half = half * (pplus.value - pminus.value) := by
  constructor
  · rw [superComm_odd_odd x y hx hy, hplus, hminus]
  · simp [superJordan, hx, hy, hplus, hminus]

/-- The super-Lie bracket is graded skew-symmetric on homogeneous elements. -/
theorem superComm_graded_skew (x y : Homogeneous A) :
    superComm x y =
      if x.degree && y.degree then superComm y x
      else -superComm y x := by
  cases hx : x.degree <;> cases hy : y.degree <;>
    (simp [superComm, hx, hy] <;> abel)

end InfoGeometry.Canonical.SupergradedRelationalSplit
