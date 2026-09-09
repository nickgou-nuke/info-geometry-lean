import Mathlib
open Matrix
open scoped Matrix

/--
`trace_comm` states that the trace of a product of two square matrices is commutative:
`trace(A * B) = trace(B * A)` for any square matrices over a commutative ring.

This follows directly from `trace_mul_comm` in Mathlib, which is even more general:
it holds for any `A : Matrix m n R` and `B : Matrix n m R` (rectangular matrices).
-/
theorem trace_comm (n : Type) [Fintype n] [DecidableEq n] (R : Type) [CommRing R] (A B : Matrix n n R) :
    trace (A * B) = trace (B * A) :=
by
  simpa using trace_mul_comm A B
