import Mathlib.Tactic
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.ModularLorentzBoost

/-!
# InfoGeometry.Canonical.SplitCliffordChiralProjection

Concrete chiral projector identities in `M₂(ℝ)`.

This file proves:

* `K = N_left - N_right`;
* `P_L = (1 + K)/2 = N_left`;
* `P_R = (1 - K)/2 = N_right`;
* orthogonality of `P_L, P_R`.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.SplitCliffordChiralProjection

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ModularLorentzBoost

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Left chiral number operator `N_left = a† a = N Nᵀ`. -/
noncomputable def N_left : M2R := N * Nᵀ

/-- Right chiral number operator `N_right = a a† = Nᵀ N`. -/
noncomputable def N_right : M2R := Nᵀ * N

@[simp]
theorem N_left_eval : N_left = !![(1 : ℝ), 0; 0, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N_left, N, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem N_right_eval : N_right = !![(0 : ℝ), 0; 0, 1] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N_right, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Modular Hamiltonian as chiral number difference. -/
theorem K_eq_chiral_difference : K = N_left - N_right := by
  rw [K_eval, N_left_eval, N_right_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

/-- Left chiral projector `P_L = (1 + K)/2`. -/
noncomputable def P_L : M2R := (1 / 2 : ℝ) • ((1 : M2R) + K)

/-- Right chiral projector `P_R = (1 - K)/2`. -/
noncomputable def P_R : M2R := (1 / 2 : ℝ) • ((1 : M2R) - K)

@[simp]
theorem P_L_spec : P_L = N_left := by
  rw [P_L, K_eval, N_left_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

@[simp]
theorem P_R_spec : P_R = N_right := by
  rw [P_R, K_eval, N_right_eval]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

/-- Chiral projectors are orthogonal. -/
theorem chiral_projector_orthogonal :
    P_L * P_R = 0 ∧ P_R * P_L = 0 := by
  constructor
  · rw [P_L_spec, P_R_spec, N_left_eval, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [P_L_spec, P_R_spec, N_left_eval, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Chiral projectors are complete and idempotent. -/
theorem chiral_projector_complete_idempotent :
    P_L + P_R = (1 : M2R) ∧ P_L * P_L = P_L ∧ P_R * P_R = P_R := by
  constructor
  · rw [P_L_spec, P_R_spec, N_left_eval, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;> norm_num
  constructor
  · rw [P_L_spec, N_left_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [P_R_spec, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem K_sq_eq_one :
    K * K = (1 : M2R) := by
  have hK : K = P_L - P_R := by
    rw [P_L_spec, P_R_spec]
    exact K_eq_chiral_difference
  obtain ⟨hSum, hL, hR⟩ := chiral_projector_complete_idempotent
  obtain ⟨hLR, hRL⟩ := chiral_projector_orthogonal
  rw [hK]
  calc
    (P_L - P_R) * (P_L - P_R) =
        P_L * P_L - (P_L * P_R + P_R * P_L) + P_R * P_R := by
          noncomm_ring
    _ = P_L + P_R := by rw [hL, hR, hLR, hRL]; simp
    _ = 1 := hSum

/-- `P_L` and `P_R` are `±1` eigenprojectors for the modular generator `K`. -/
theorem K_mul_chiral_projectors :
    K * P_L = P_L ∧ K * P_R = -P_R := by
  constructor
  · rw [K_eval, P_L_spec, N_left_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [K_eval, P_R_spec, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Chiral projectors commute with the modular generator. -/
theorem K_commutes_chiral_projectors :
    K * P_L - P_L * K = 0 ∧ K * P_R - P_R * K = 0 := by
  constructor
  · rw [K_eval, P_L_spec, N_left_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [K_eval, P_R_spec, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Right-action eigenprojector laws for the modular generator. -/
theorem chiral_projectors_mul_K :
    P_L * K = P_L ∧ P_R * K = -P_R := by
  constructor
  · rw [K_eval, P_L_spec, N_left_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [K_eval, P_R_spec, N_right_eval]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The raising matrix has positive left and negative right `K` weight. -/
theorem K_mul_N : K * N = N := by
  rw [K_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_mul_K : N * K = -N := by
  rw [K_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lowering matrix has negative left and positive right `K` weight. -/
theorem K_mul_N_transpose : K * Nᵀ = -Nᵀ := by
  rw [K_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_transpose_mul_K : Nᵀ * K = Nᵀ := by
  rw [K_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem N_sq : N * N = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem N_transpose_sq : Nᵀ * Nᵀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_commutator : N * Nᵀ - Nᵀ * N = K := by
  rw [K_eq_chiral_difference]
  rfl

theorem N_anticommutator : N * Nᵀ + Nᵀ * N = (1 : M2R) := by
  change N_left + N_right = (1 : M2R)
  rw [N_left_eval, N_right_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem P_L_mul_N : P_L * N = N := by
  rw [P_L_spec, N_left_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_mul_P_R : N * P_R = N := by
  rw [P_R_spec, N_right_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_R_mul_N_transpose : P_R * Nᵀ = Nᵀ := by
  rw [P_R_spec, N_right_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_transpose_mul_P_L : Nᵀ * P_L = Nᵀ := by
  rw [P_L_spec, N_left_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_R_mul_N : P_R * N = 0 := by
  rw [P_R_spec, N_right_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_mul_P_L : N * P_L = 0 := by
  rw [P_L_spec, N_left_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_L_mul_N_transpose : P_L * Nᵀ = 0 := by
  rw [P_L_spec, N_left_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_transpose_mul_P_R : Nᵀ * P_R = 0 := by
  rw [P_R_spec, N_right_eval]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.SplitCliffordChiralProjection
