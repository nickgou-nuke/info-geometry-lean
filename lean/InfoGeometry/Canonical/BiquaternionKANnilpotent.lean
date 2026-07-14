import Mathlib

/-!
# Biquaternion KAN nilpotent atom

Recovered owner for the finite `2 × 2` nilpotent KAN anchor found in the
archive/removable-disk lane. This module proves only the explicit algebraic
square-zero facts for the upper-triangular nilpotent atom and its scaled copies.
It does not assert analytic KAN, modular-flow, or continuum geometry claims.
-/

namespace BiquaternionKANnilpotent

open Matrix Complex

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The nilpotent `N` atom in an upper-triangular KAN chart. -/
def K_N : M2C := !![0, 1; 0, 0]

/-- The KAN nilpotent atom squares to zero. -/
theorem K_N_is_nilpotent : K_N * K_N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [K_N, Matrix.mul_apply]

/-- Truncated exponential for a square-zero nilpotent: `exp₂ N = I + N`. -/
def exp_K_N : M2C := 1 + K_N

/-- Every scalar multiple of the KAN nilpotent atom is still square-zero. -/
theorem scaled_K_N_is_nilpotent (ε : ℂ) :
    (ε • K_N) * (ε • K_N) = 0 := by
  calc
    (ε • K_N) * (ε • K_N) = (ε * ε) • (K_N * K_N) := by
      rw [smul_mul_smul]
    _ = (ε * ε) • (0 : M2C) := by rw [K_N_is_nilpotent]
    _ = 0 := by simp

/-- Consolidated finite KAN-nilpotent certificate. -/
theorem kan_nilpotent_synthesis :
    K_N * K_N = 0 ∧ (∀ ε : ℂ, (ε • K_N) * (ε • K_N) = 0) := by
  exact ⟨K_N_is_nilpotent, scaled_K_N_is_nilpotent⟩

end BiquaternionKANnilpotent