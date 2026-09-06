import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Field.Basic

open Matrix

namespace UnitTraceNormalization

variable {d : ℕ} {K : Type*} [Field K]

/-- Normalized trace operator for d × d matrices: τ_d(M) = (1 / d) * Tr(M) -/
def normalizedTrace (d : ℕ) (M : Matrix (Fin d) (Fin d) K) : K :=
  (1 / (d : K)) * trace M

/-- 🏆 THEOREM: Unit Matrix Trace Normalization τ_d(I) = 1
    Proves that the normalized trace of the d × d identity matrix equals 1
    for any non-zero dimension d (d : K ≠ 0). -/
theorem normalizedTrace_identity (hd : (d : K) ≠ 0) :
    normalizedTrace d (1 : Matrix (Fin d) (Fin d) K) = 1 := by
  dsimp [normalizedTrace]
  rw [trace_one]
  simp only [Fintype.card_fin]
  exact one_div_mul_cancel hd

end UnitTraceNormalization
