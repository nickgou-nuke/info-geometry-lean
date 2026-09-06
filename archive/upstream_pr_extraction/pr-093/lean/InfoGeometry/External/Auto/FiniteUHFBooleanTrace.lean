import Mathlib.Tactic

/-!
# Finite UHF Boolean Trace

This module generalizes the symbolic-lane/UHF-boundary bridge from explicit
two- and three-coordinate traces to an arbitrary finite list of weights.

The finite Boolean trace is the recursive sum over the next UHF diagonal bit:

`Trace([]) = 1`

`Trace(x :: xs) = Trace(xs) + (-x) * Trace(xs)`

Therefore `Trace(xs) = ∏ᵢ (1 - xᵢ)`, the finite graded Fock determinant.
-/

noncomputable section

namespace FiniteUHFBooleanTrace

/-- Local graded boundary selector: empty bit gives `1`, occupied bit gives `-x`. -/
def gradedBitSelector (bit : Bool) (x : ℂ) : ℂ :=
  if bit then -x else 1

/-- Recursive finite Boolean trace over UHF diagonal bits. -/
def finiteBooleanTrace : List ℂ → ℂ
  | [] => 1
  | x :: xs => finiteBooleanTrace xs + (-x) * finiteBooleanTrace xs

/-- Finite graded product/determinant. -/
def gradedProduct (xs : List ℂ) : ℂ :=
  xs.map (fun x => 1 - x) |>.prod

theorem gradedBitSelector_false (x : ℂ) :
    gradedBitSelector false x = 1 := by
  simp [gradedBitSelector]

theorem gradedBitSelector_true (x : ℂ) :
    gradedBitSelector true x = -x := by
  simp [gradedBitSelector]

theorem finiteBooleanTrace_nil :
    finiteBooleanTrace [] = 1 := rfl

theorem finiteBooleanTrace_cons (x : ℂ) (xs : List ℂ) :
    finiteBooleanTrace (x :: xs) =
      finiteBooleanTrace xs + (-x) * finiteBooleanTrace xs := rfl

/-- Arbitrary finite UHF Boolean trace equals the finite graded determinant. -/
theorem finiteBooleanTrace_eq_gradedProduct (xs : List ℂ) :
    finiteBooleanTrace xs = gradedProduct xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [finiteBooleanTrace, gradedProduct, ih]
      ring

/-- Adding a new UHF bit/prime mode appends one local factor. -/
theorem finiteBooleanTrace_snoc (xs : List ℂ) (x : ℂ) :
    finiteBooleanTrace (xs ++ [x]) =
      finiteBooleanTrace xs * (1 - x) := by
  rw [finiteBooleanTrace_eq_gradedProduct xs]
  rw [finiteBooleanTrace_eq_gradedProduct (xs ++ [x])]
  induction xs with
  | nil =>
      simp [gradedProduct]
  | cons y ys ih =>
      simp [gradedProduct]
      ring

/-- One-coordinate trace. -/
theorem one_coordinate_trace (x : ℂ) :
    gradedBitSelector false x + gradedBitSelector true x = 1 - x := by
  simp [gradedBitSelector]
  ring

/-- Two-coordinate trace factors through the recursive trace. -/
theorem two_coordinate_trace (x y : ℂ) :
    (gradedBitSelector false x * gradedBitSelector false y) +
      (gradedBitSelector false x * gradedBitSelector true y) +
      (gradedBitSelector true x * gradedBitSelector false y) +
      (gradedBitSelector true x * gradedBitSelector true y)
      =
    finiteBooleanTrace [x, y] := by
  simp [gradedBitSelector, finiteBooleanTrace]
  ring

/-- Three-coordinate trace factors through the recursive trace. -/
theorem three_coordinate_trace (x y z : ℂ) :
    (gradedBitSelector false x * gradedBitSelector false y * gradedBitSelector false z) +
      (gradedBitSelector false x * gradedBitSelector false y * gradedBitSelector true z) +
      (gradedBitSelector false x * gradedBitSelector true y * gradedBitSelector false z) +
      (gradedBitSelector false x * gradedBitSelector true y * gradedBitSelector true z) +
      (gradedBitSelector true x * gradedBitSelector false y * gradedBitSelector false z) +
      (gradedBitSelector true x * gradedBitSelector false y * gradedBitSelector true z) +
      (gradedBitSelector true x * gradedBitSelector true y * gradedBitSelector false z) +
      (gradedBitSelector true x * gradedBitSelector true y * gradedBitSelector true z)
      =
    finiteBooleanTrace [x, y, z] := by
  simp [gradedBitSelector, finiteBooleanTrace]
  ring

end FiniteUHFBooleanTrace

end noncomputable section
