import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# Grassmannian Grothendieck Ring Elimination for `Gr(2,4)`

This file proves the finite algebraic elimination step for the coefficient
relations obtained from

`(1 + e_1 X + e_2 X^2) * (1 + f_1 X + f_2 X^2) = (1 + X)^4`.

The hypotheses are the four coefficient equations. The theorems prove that
`f_1` and `f_2` are forced by `e_1` and `e_2`, and that the third and fourth
relations reduce to polynomial equations in `e_1` and `e_2`.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `f1_eq`, `f2_eq`, `rel3_elim`, `rel4_elim`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES: None.
- BUCKET 3: OPEN CLOSURE DEBT: None.
-/

namespace GrassmannianGrothendieckRing

variable {R : Type*} [CommRing R]

/-- The class `f_1` is uniquely determined by the generator `e_1`. -/
theorem f1_eq (e_1 f_1 : R) (h1 : e_1 + f_1 = 4) : f_1 = 4 - e_1 := by
  calc
    f_1 = (e_1 + f_1) - e_1 := by ring
    _ = 4 - e_1 := by rw [h1]

/-- The class `f_2` is uniquely determined by `e_1` and `e_2`. -/
theorem f2_eq (e_1 e_2 f_1 f_2 : R)
    (h1 : e_1 + f_1 = 4)
    (h2 : e_2 + e_1 * f_1 + f_2 = 6) :
    f_2 = 6 - e_2 - 4 * e_1 + e_1 ^ 2 := by
  have hf1 : f_1 = 4 - e_1 := f1_eq e_1 f_1 h1
  calc
    f_2 = (e_2 + e_1 * f_1 + f_2) - e_2 - e_1 * f_1 := by ring
    _ = 6 - e_2 - e_1 * (4 - e_1) := by rw [h2, hf1]
    _ = 6 - e_2 - 4 * e_1 + e_1 ^ 2 := by ring

/-- Elimination of the third relation into a polynomial equation in `e_1` and `e_2`. -/
theorem rel3_elim (e_1 e_2 f_1 f_2 : R)
    (h1 : e_1 + f_1 = 4)
    (h2 : e_2 + e_1 * f_1 + f_2 = 6)
    (h3 : e_2 * f_1 + e_1 * f_2 = 4) :
    e_2 * (4 - e_1) + e_1 * (6 - e_2 - 4 * e_1 + e_1 ^ 2) = 4 := by
  have hf1 : f_1 = 4 - e_1 := f1_eq e_1 f_1 h1
  have hf2 : f_2 = 6 - e_2 - 4 * e_1 + e_1 ^ 2 := f2_eq e_1 e_2 f_1 f_2 h1 h2
  calc
    e_2 * (4 - e_1) + e_1 * (6 - e_2 - 4 * e_1 + e_1 ^ 2)
        = e_2 * f_1 + e_1 * f_2 := by rw [← hf1, ← hf2]
    _ = 4 := h3

/-- Elimination of the fourth relation into a polynomial equation in `e_1` and `e_2`. -/
theorem rel4_elim (e_1 e_2 f_1 f_2 : R)
    (h1 : e_1 + f_1 = 4)
    (h2 : e_2 + e_1 * f_1 + f_2 = 6)
    (h4 : e_2 * f_2 = 1) :
    e_2 * (6 - e_2 - 4 * e_1 + e_1 ^ 2) = 1 := by
  have hf2 : f_2 = 6 - e_2 - 4 * e_1 + e_1 ^ 2 := f2_eq e_1 e_2 f_1 f_2 h1 h2
  calc
    e_2 * (6 - e_2 - 4 * e_1 + e_1 ^ 2) = e_2 * f_2 := by rw [← hf2]
    _ = 1 := h4

end GrassmannianGrothendieckRing
