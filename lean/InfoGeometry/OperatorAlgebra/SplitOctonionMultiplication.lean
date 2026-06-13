import Mathlib.Tactic

/-!
# True split-octonion multiplication layer

This module is the Lean twin of `tools/sympy/split_octonion_multiplication.py`.
It defines an explicit eight-coordinate Zorn split-octonion carrier over `ℤ`
and a concrete nonassociative multiplication table:

```text
(a,x;y,b)(c,u;v,d) =
  (a c + x·v,
   a u + d x - y×v;
   b v + c y + x×u,
   b d + y·u)
```

Theorems below lock the basis table, idempotent diagonal units, nilpotent
upper/lower units, a concrete nonzero associator witness, and basis
alternativity checks.  This is a multiplication layer only: it does not assert a
`G₂(2)` automorphism theorem, an `SU(3)` stabilizer theorem, or a particle
classification theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- Eight-coordinate Zorn split-octonion cell over `ℤ`. -/
structure SplitOct where
  a : ℤ
  b : ℤ
  x0 : ℤ
  x1 : ℤ
  x2 : ℤ
  y0 : ℤ
  y1 : ℤ
  y2 : ℤ
  deriving DecidableEq, Repr

/-- Coordinatewise zero. -/
def zeroZ : SplitOct := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Coordinatewise negation. -/
def negZ (X : SplitOct) : SplitOct :=
  ⟨-X.a, -X.b, -X.x0, -X.x1, -X.x2, -X.y0, -X.y1, -X.y2⟩

/-- Coordinatewise subtraction. -/
def subZ (X Y : SplitOct) : SplitOct :=
  ⟨X.a - Y.a, X.b - Y.b, X.x0 - Y.x0, X.x1 - Y.x1, X.x2 - Y.x2,
    X.y0 - Y.y0, X.y1 - Y.y1, X.y2 - Y.y2⟩

/-- Zorn determinant / split norm. -/
def detZ (X : SplitOct) : ℤ :=
  X.a * X.b - (X.x0 * X.y0 + X.x1 * X.y1 + X.x2 * X.y2)

/-- True Zorn split-octonion multiplication. -/
def mulZ (X Y : SplitOct) : SplitOct :=
  ⟨ X.a * Y.a + (X.x0 * Y.y0 + X.x1 * Y.y1 + X.x2 * Y.y2),
    X.b * Y.b + (X.y0 * Y.x0 + X.y1 * Y.x1 + X.y2 * Y.x2),
    X.a * Y.x0 + Y.b * X.x0 - (X.y1 * Y.y2 - X.y2 * Y.y1),
    X.a * Y.x1 + Y.b * X.x1 - (X.y2 * Y.y0 - X.y0 * Y.y2),
    X.a * Y.x2 + Y.b * X.x2 - (X.y0 * Y.y1 - X.y1 * Y.y0),
    X.b * Y.y0 + Y.a * X.y0 + (X.x1 * Y.x2 - X.x2 * Y.x1),
    X.b * Y.y1 + Y.a * X.y1 + (X.x2 * Y.x0 - X.x0 * Y.x2),
    X.b * Y.y2 + Y.a * X.y2 + (X.x0 * Y.x1 - X.x1 * Y.x0) ⟩

/-- Coordinate associator `(xy)z - x(yz)`. -/
def associator (X Y Z : SplitOct) : SplitOct := subZ (mulZ (mulZ X Y) Z) (mulZ X (mulZ Y Z))

/-- First diagonal idempotent. -/
def ePlus : SplitOct := ⟨1, 0, 0, 0, 0, 0, 0, 0⟩

/-- Second diagonal idempotent. -/
def eMinus : SplitOct := ⟨0, 1, 0, 0, 0, 0, 0, 0⟩

/-- Upper Zorn vector units. -/
def up0 : SplitOct := ⟨0, 0, 1, 0, 0, 0, 0, 0⟩
def up1 : SplitOct := ⟨0, 0, 0, 1, 0, 0, 0, 0⟩
def up2 : SplitOct := ⟨0, 0, 0, 0, 1, 0, 0, 0⟩

/-- Lower Zorn vector units. -/
def down0 : SplitOct := ⟨0, 0, 0, 0, 0, 1, 0, 0⟩
def down1 : SplitOct := ⟨0, 0, 0, 0, 0, 0, 1, 0⟩
def down2 : SplitOct := ⟨0, 0, 0, 0, 0, 0, 0, 1⟩

/-- Index readout for upper units. -/
def up : Fin 3 → SplitOct
  | 0 => up0
  | 1 => up1
  | 2 => up2

/-- Index readout for lower units. -/
def down : Fin 3 → SplitOct
  | 0 => down0
  | 1 => down1
  | 2 => down2

theorem ePlus_idempotent : mulZ ePlus ePlus = ePlus := by decide
theorem eMinus_idempotent : mulZ eMinus eMinus = eMinus := by decide
theorem ePlus_mul_eMinus : mulZ ePlus eMinus = zeroZ := by decide
theorem eMinus_mul_ePlus : mulZ eMinus ePlus = zeroZ := by decide

theorem ePlus_mul_up (i : Fin 3) : mulZ ePlus (up i) = up i := by
  fin_cases i <;> decide
theorem eMinus_mul_up_zero (i : Fin 3) : mulZ eMinus (up i) = zeroZ := by
  fin_cases i <;> decide
theorem up_mul_eMinus (i : Fin 3) : mulZ (up i) eMinus = up i := by
  fin_cases i <;> decide
theorem up_mul_ePlus_zero (i : Fin 3) : mulZ (up i) ePlus = zeroZ := by
  fin_cases i <;> decide

theorem eMinus_mul_down (i : Fin 3) : mulZ eMinus (down i) = down i := by
  fin_cases i <;> decide
theorem ePlus_mul_down_zero (i : Fin 3) : mulZ ePlus (down i) = zeroZ := by
  fin_cases i <;> decide
theorem down_mul_ePlus (i : Fin 3) : mulZ (down i) ePlus = down i := by
  fin_cases i <;> decide
theorem down_mul_eMinus_zero (i : Fin 3) : mulZ (down i) eMinus = zeroZ := by
  fin_cases i <;> decide

theorem up_sq_zero (i : Fin 3) : mulZ (up i) (up i) = zeroZ := by
  fin_cases i <;> decide
theorem down_sq_zero (i : Fin 3) : mulZ (down i) (down i) = zeroZ := by
  fin_cases i <;> decide
theorem up_mul_down_same (i : Fin 3) : mulZ (up i) (down i) = ePlus := by
  fin_cases i <;> decide
theorem down_mul_up_same (i : Fin 3) : mulZ (down i) (up i) = eMinus := by
  fin_cases i <;> decide

theorem up0_mul_up1 : mulZ up0 up1 = down2 := by decide
theorem up1_mul_up2 : mulZ up1 up2 = down0 := by decide
theorem up2_mul_up0 : mulZ up2 up0 = down1 := by decide
theorem up1_mul_up0 : mulZ up1 up0 = negZ down2 := by decide
theorem up2_mul_up1 : mulZ up2 up1 = negZ down0 := by decide
theorem up0_mul_up2 : mulZ up0 up2 = negZ down1 := by decide

theorem down0_mul_down1 : mulZ down0 down1 = negZ up2 := by decide
theorem down1_mul_down2 : mulZ down1 down2 = negZ up0 := by decide
theorem down2_mul_down0 : mulZ down2 down0 = negZ up1 := by decide
theorem down1_mul_down0 : mulZ down1 down0 = up2 := by decide
theorem down2_mul_down1 : mulZ down2 down1 = up0 := by decide
theorem down0_mul_down2 : mulZ down0 down2 = up1 := by decide

/-- Concrete nonassociativity witness: `(u₀u₁)v₁ - u₀(u₁v₁) = u₀`. -/
theorem associator_up0_up1_down1 : associator up0 up1 down1 = up0 := by decide

/-- The concrete associator witness is nonzero. -/
theorem associator_up0_up1_down1_ne_zero : associator up0 up1 down1 ≠ zeroZ := by decide

/-- Basis left-alternativity check for upper units against upper units. -/
theorem up_left_alternative_on_up (i j : Fin 3) : associator (up i) (up i) (up j) = zeroZ := by
  fin_cases i <;> fin_cases j <;> decide

/-- Basis right-alternativity check for upper units against upper units. -/
theorem up_right_alternative_on_up (i j : Fin 3) : associator (up j) (up i) (up i) = zeroZ := by
  fin_cases i <;> fin_cases j <;> decide

/-- Basis left-alternativity check for lower units against lower units. -/
theorem down_left_alternative_on_down (i j : Fin 3) : associator (down i) (down i) (down j) = zeroZ := by
  fin_cases i <;> fin_cases j <;> decide

/-- Basis right-alternativity check for lower units against lower units. -/
theorem down_right_alternative_on_down (i j : Fin 3) : associator (down j) (down i) (down i) = zeroZ := by
  fin_cases i <;> fin_cases j <;> decide

theorem detZ_ePlus : detZ ePlus = 0 := by decide
theorem detZ_eMinus : detZ eMinus = 0 := by decide
theorem detZ_up (i : Fin 3) : detZ (up i) = 0 := by
  fin_cases i <;> decide
theorem detZ_down (i : Fin 3) : detZ (down i) = 0 := by
  fin_cases i <;> decide

/-- Closed kernel packet for the true split-octonion basis multiplication surface. -/
theorem splitOctonion_multiplication_packet :
    mulZ ePlus ePlus = ePlus ∧
      mulZ eMinus eMinus = eMinus ∧
      mulZ ePlus eMinus = zeroZ ∧
      mulZ eMinus ePlus = zeroZ ∧
      (∀ i : Fin 3, mulZ (up i) (up i) = zeroZ) ∧
      (∀ i : Fin 3, mulZ (down i) (down i) = zeroZ) ∧
      (∀ i : Fin 3, mulZ (up i) (down i) = ePlus) ∧
      (∀ i : Fin 3, mulZ (down i) (up i) = eMinus) ∧
      mulZ up0 up1 = down2 ∧
      mulZ down0 down1 = negZ up2 ∧
      associator up0 up1 down1 = up0 ∧
      associator up0 up1 down1 ≠ zeroZ := by
  exact ⟨ePlus_idempotent, eMinus_idempotent, ePlus_mul_eMinus, eMinus_mul_ePlus,
    up_sq_zero, down_sq_zero, up_mul_down_same, down_mul_up_same,
    up0_mul_up1, down0_mul_down1, associator_up0_up1_down1,
    associator_up0_up1_down1_ne_zero⟩

end InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
