import Mathlib

/-!
# Finite TKK closure interface

The former owner mixed declarations, prose, and ill-typed placeholders.  This
module keeps the kernel-level content: a five-graded carrier and the native
grade arithmetic.  Lie brackets and geometric identifications require an
explicit supplied bracket and are intentionally not inferred here.
-/

namespace TKKClosureErlangenGeometry

inductive Grade where
  | neg2 | neg1 | zero | pos1 | pos2
  deriving DecidableEq, Repr

def gradeValue : Grade → ℤ
  | .neg2 => -2
  | .neg1 => -1
  | .zero => 0
  | .pos1 => 1
  | .pos2 => 2

theorem gradeValue_neg2 : gradeValue .neg2 = -2 := rfl
theorem gradeValue_neg1 : gradeValue .neg1 = -1 := rfl
theorem gradeValue_zero : gradeValue .zero = 0 := rfl
theorem gradeValue_pos1 : gradeValue .pos1 = 1 := rfl
theorem gradeValue_pos2 : gradeValue .pos2 = 2 := rfl

def gradeNeg : Grade → Grade
  | .neg2 => .pos2
  | .neg1 => .pos1
  | .zero => .zero
  | .pos1 => .neg1
  | .pos2 => .neg2

theorem gradeNeg_involutive (g : Grade) : gradeNeg (gradeNeg g) = g := by
  cases g <;> rfl

theorem gradeNeg_value (g : Grade) : gradeValue (gradeNeg g) = -gradeValue g := by
  cases g <;> rfl

def gradeCarrier (V : Type*) := Grade → V

end TKKClosureErlangenGeometry
