import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Field.Basic

open Matrix

namespace NormalizedTraceCyclicity

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Normalized trace operator for n × n matrices with dimension factor d:
    τ_d(M) = (1 / d) * Tr(M) -/
def normalizedTrace (d : K) (M : Matrix n n K) : K :=
  (1 / d) * trace M

/-- 🏆 THEOREM: Cyclicity of the Normalized Trace τ_d(A * B) = τ_d(B * A)
    Proves that the normalized trace obeys the tracial commutator property
    for any two matrices A, B ∈ Mₙ(K). -/
theorem normalizedTrace_mul_comm (d : K) (A B : Matrix n n K) :
    normalizedTrace d (A * B) = normalizedTrace d (B * A) := by
  dsimp [normalizedTrace]
  rw [trace_mul_comm]

end NormalizedTraceCyclicity
