import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# The integral Zorn split-octonion order

This is the honest integral order underlying the existing `SplitOct` owner
file.  It is the split-octonion analogue of the Lipschitz starting order.  No
maximal-order or lattice-identification claim is made here.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.IntegerOrder

/-- Integer Zorn coordinates: two scalars and two integral three-vectors. -/
structure ZornIntegerSplitOctonion where
  a : ℤ
  b : ℤ
  v : Fin 3 → ℤ
  w : Fin 3 → ℤ
  deriving DecidableEq

def toSplitOct (x : ZornIntegerSplitOctonion) : SplitOct :=
  { a := x.a, b := x.b,
    x0 := x.v 0, x1 := x.v 1, x2 := x.v 2,
    y0 := x.w 0, y1 := x.w 1, y2 := x.w 2 }

def ofSplitOct (x : SplitOct) : ZornIntegerSplitOctonion :=
  { a := x.a, b := x.b,
    v := ![x.x0, x.x1, x.x2],
    w := ![x.y0, x.y1, x.y2] }

theorem ofSplitOct_toSplitOct (x : ZornIntegerSplitOctonion) :
    ofSplitOct (toSplitOct x) = x := by
  cases x with
  | mk a b v w =>
    change
      ({ a := a, b := b, v := ![v 0, v 1, v 2], w := ![w 0, w 1, w 2] } :
        ZornIntegerSplitOctonion) =
        ({ a := a, b := b, v := v, w := w } : ZornIntegerSplitOctonion)
    congr 1
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl

theorem toSplitOct_ofSplitOct (x : SplitOct) :
    toSplitOct (ofSplitOct x) = x := by
  cases x
  rfl

def zero : ZornIntegerSplitOctonion := ofSplitOct zeroZ

def mul (x y : ZornIntegerSplitOctonion) : ZornIntegerSplitOctonion :=
  ofSplitOct (mulZ (toSplitOct x) (toSplitOct y))

def norm (x : ZornIntegerSplitOctonion) : ℤ :=
  detZ (toSplitOct x)

def trace (x : ZornIntegerSplitOctonion) : ℤ :=
  x.a + x.b

def conjugate (x : ZornIntegerSplitOctonion) : ZornIntegerSplitOctonion :=
  ofSplitOct (conjZ (toSplitOct x))

/-- The Zorn product stays in the integral coordinate order. -/
theorem mul_closed (x y : ZornIntegerSplitOctonion) :
    mul x y = ofSplitOct (mulZ (toSplitOct x) (toSplitOct y)) := rfl

/-- The integral order has an integral norm. -/
theorem norm_eq_det (x : ZornIntegerSplitOctonion) :
    norm x = detZ (toSplitOct x) := rfl

/-- Coordinate form of the integral Zorn norm. -/
theorem norm_eq_coordinate_formula (x : ZornIntegerSplitOctonion) :
    norm x = x.a * x.b -
      (x.v 0 * x.w 0 + x.v 1 * x.w 1 + x.v 2 * x.w 2) := rfl

/-- The same norm written as a finite sum over the three vector coordinates. -/
theorem norm_eq_fin_sum (x : ZornIntegerSplitOctonion) :
    norm x = x.a * x.b - ∑ i : Fin 3, x.v i * x.w i := by
  rw [norm_eq_coordinate_formula]
  simp [Fin.sum_univ_succ]
  ring

/-- Norm multiplicativity is inherited from the concrete Zorn model. -/
theorem norm_mul (x y : ZornIntegerSplitOctonion) :
    norm (mul x y) = norm x * norm y := by
  rw [norm, mul]
  simp only [toSplitOct_ofSplitOct]
  exact detZ_mul (toSplitOct x) (toSplitOct y)

/-- Conjugation preserves the integral norm. -/
theorem norm_conjugate (x : ZornIntegerSplitOctonion) :
    norm (conjugate x) = norm x := by
  rw [norm, conjugate]
  dsimp [toSplitOct, conjZ, ofSplitOct, detZ]
  rw [norm_eq_coordinate_formula]
  ring

/-- The norm is the scalar part of multiplication by the conjugate. -/
theorem mul_conjugate (x : ZornIntegerSplitOctonion) :
    mul x (conjugate x) = ofSplitOct (scalarZ (norm x)) := by
  unfold mul conjugate norm
  rw [toSplitOct_ofSplitOct]
  exact congrArg ofSplitOct (mul_conjZ_eq_scalar_detZ (toSplitOct x))

/-- The trace is the sum of the two Zorn diagonal coordinates. -/
theorem trace_eq_diagonal (x : ZornIntegerSplitOctonion) :
    trace x = x.a + x.b := rfl

end InfoGeometry.OperatorAlgebra.SplitOctonions.IntegerOrder
