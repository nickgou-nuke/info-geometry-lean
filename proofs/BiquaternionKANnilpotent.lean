import Mathlib

/-!
# A square-zero `2 × 2` complex matrix
-/

namespace BiquaternionKANnilpotent

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The basic upper nilpotent `2 × 2` complex matrix. -/
def K_N : M2C := !![0, 1; 0, 0]

/-- `K_N` squares to zero. -/
theorem K_N_sq : K_N * K_N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [K_N, Matrix.mul_apply]

/-- Every scalar multiple of `K_N` squares to zero. -/
theorem scalar_K_N_sq (ε : ℂ) :
    (ε • K_N) * (ε • K_N) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [K_N, Matrix.mul_apply]

/-- The square-zero identities for `K_N`. -/
theorem kan_nilpotent_identities :
    K_N * K_N = 0 ∧ (∀ ε : ℂ, (ε • K_N) * (ε • K_N) = 0) := by
  exact ⟨K_N_sq, scalar_K_N_sq⟩

end BiquaternionKANnilpotent
