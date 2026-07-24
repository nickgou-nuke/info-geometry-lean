import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic

/-!
# The Finite Matrix Lie Algebra `sl_n`

This file defines a custom diagonal-sum trace `my_trace` and proves finite
trace laws for matrices over a commutative ring. The main result is that every
matrix commutator has trace zero, hence belongs to the special linear Lie
algebra submodule of trace-zero matrices.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `my_trace`, `my_trace_add`, `my_trace_sub`, `my_trace_smul`,
  `my_trace_mul_comm`, `my_trace_commutator`, `SlLieAlgebra`,
  `commutator_mem_sl`, `lie_bracket_closed`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES: None.
- BUCKET 3: OPEN CLOSURE DEBT: None.
-/

namespace InfoGeometry.Canonical.SpecialLinearLieAlgebra

open BigOperators

variable {n : Type*} [Fintype n]
variable {F : Type*} [CommRing F]

/-- The custom trace operator defined as the sum of diagonal entries. -/
def my_trace (A : Matrix n n F) : F :=
  ∑ i, A i i

theorem my_trace_eq_matrix_trace (A : Matrix n n F) :
    my_trace A = Matrix.trace A := by
  simp [my_trace, Matrix.trace, Matrix.diag]

/-- The trace of a sum is the sum of traces. -/
lemma my_trace_add (A B : Matrix n n F) :
    my_trace (A + B) = my_trace A + my_trace B := by
  simp [my_trace_eq_matrix_trace]

/-- The trace of a difference is the difference of traces. -/
lemma my_trace_sub (A B : Matrix n n F) :
    my_trace (A - B) = my_trace A - my_trace B := by
  simp [my_trace_eq_matrix_trace]

/-- The trace of a scaled matrix is the scaled trace. -/
lemma my_trace_smul (c : F) (A : Matrix n n F) :
    my_trace (c • A) = c * my_trace A := by
  simp [my_trace_eq_matrix_trace, smul_eq_mul]

/-- The cyclic property of the trace operator: `trace (A * B) = trace (B * A)`. -/
lemma my_trace_mul_comm (A B : Matrix n n F) :
    my_trace (A * B) = my_trace (B * A) := by
  simpa [my_trace_eq_matrix_trace] using Matrix.trace_mul_comm A B

/-- The trace of any commutator `[A, B] = A * B - B * A` is zero. -/
theorem my_trace_commutator (A B : Matrix n n F) :
    my_trace (A * B - B * A) = 0 := by
  rw [my_trace_sub, my_trace_mul_comm]
  exact sub_self (my_trace (B * A))

/-- The special linear Lie algebra: the submodule of trace-zero matrices. -/
def SlLieAlgebra (n : Type*) [Fintype n] (F : Type*) [CommRing F] :
    Submodule F (Matrix n n F) where
  carrier := {A | my_trace A = 0}
  zero_mem' := by
    simp [my_trace]
  add_mem' := by
    intro A B hA hB
    rw [Set.mem_setOf_eq] at hA hB
    rw [Set.mem_setOf_eq, my_trace_add, hA, hB, add_zero]
  smul_mem' := by
    intro c A hA
    rw [Set.mem_setOf_eq] at hA
    rw [Set.mem_setOf_eq, my_trace_smul, hA, mul_zero]

/-- The commutator of any two matrices lies in the special linear Lie algebra. -/
theorem commutator_mem_sl (A B : Matrix n n F) :
    A * B - B * A ∈ SlLieAlgebra n F := by
  exact my_trace_commutator A B

/-- The special linear Lie algebra is closed under the commutator bracket. -/
theorem lie_bracket_closed {A B : Matrix n n F}
    (_hA : A ∈ SlLieAlgebra n F) (_hB : B ∈ SlLieAlgebra n F) :
    A * B - B * A ∈ SlLieAlgebra n F := by
  exact commutator_mem_sl A B

end InfoGeometry.Canonical.SpecialLinearLieAlgebra
