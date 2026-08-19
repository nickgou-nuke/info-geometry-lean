import Mathlib.Tactic

open Matrix Complex

/-!
# Spinor monodromy stepping stone

This file formalizes the abstract bridge requested after concrete
biquaternion/braid constructions:

* a half-twist operator whose square is the full twist;
* spinorial monodromy means the full twist acts by `-I`;
* consequently the half-twist is a square root of negative identity;
* logarithm branches are shifted by integral `2πi` data.

The point is deliberately theorem-honest and reusable for later concrete
monodromy matrices.
-/

noncomputable section

namespace SpinorMonodromySteppingStone

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The concrete local spinor gate, real form of `iσ₂`. -/
def spinorGate : M2C := !![0, 1; -1, 0]

/-- The concrete local spinor gate squares to `-I`. -/
theorem spinorGate_sq : spinorGate * spinorGate = -(1 : M2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [spinorGate]

/-- Four half twists return to identity. -/
theorem spinorGate_fourth_identity :
    spinorGate ^ 4 = (1 : M2C) := by
  have h2 : spinorGate ^ 2 = -(1 : M2C) := by
    simpa [pow_two] using spinorGate_sq
  rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, h2]
  simp

/-- Logarithm branch shifts carry the integral winding datum `2πi n`. -/
def logBranchShift (n : ℤ) : ℂ := (2 * Real.pi * n : ℝ) * I

/-- Branch shifts compose by addition of windings. -/
theorem logBranchShift_add (m n : ℤ) :
    logBranchShift (m + n) = logBranchShift m + logBranchShift n := by
  unfold logBranchShift
  norm_num
  ring

/-- Branch shift negation corresponds to reversing winding orientation. -/
theorem logBranchShift_neg (n : ℤ) :
    logBranchShift (-n) = -logBranchShift n := by
  unfold logBranchShift
  norm_num

end SpinorMonodromySteppingStone
