import Mathlib.Tactic
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.ModularLorentzBoost

/-!
# InfoGeometry.Canonical.ModularSL2R

Concrete `sl(2, ℝ)` closure and trace-form identities for the modular boost
triple `(K, N, Nᵀ)` in `M₂(ℝ)`.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.ModularSL2R

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ModularLorentzBoost

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-! ### `sl(2, ℝ)` commutator closure -/

/-- Explicit transpose normal form of `N`. -/
noncomputable def Nt : M2R := !![0, 0; 1, 0]

@[simp]
theorem Nt_eq_transpose : Nt = Nᵀ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Nt, N, Matrix.transpose_apply]

/-- Commutator with explicit transpose normal form. -/
theorem comm_N_Nt :
    N * Nt - Nt * N = K := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Nt, K_eval, Matrix.mul_apply, Fin.sum_univ_two]

/-- Third commutator of the conformal triple: `[N, Nᵀ] = K`. -/
theorem comm_N_N_transpose :
    N * Nᵀ - Nᵀ * N = K := by
  simpa [Nt_eq_transpose] using comm_N_Nt

theorem comm_K_N :
    K * N - N * K = 2 • N := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, K_eval, Matrix.mul_apply, Fin.sum_univ_two]

theorem comm_K_N_transpose :
    K * Nᵀ - Nᵀ * K = -(2 : ℝ) • Nᵀ := by
  have h : K * Nt - Nt * K = -(2 : ℝ) • Nt := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Nt, K_eval, Matrix.mul_apply, Fin.sum_univ_two]
  simpa [Nt_eq_transpose] using h

theorem comm_N_K :
    N * K - K * N = -(2 : ℝ) • N := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, K_eval, Matrix.mul_apply, Fin.sum_univ_two]

theorem comm_N_transpose_K :
    Nᵀ * K - K * Nᵀ = (2 : ℝ) • Nᵀ := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (congrArg Neg.neg comm_K_N_transpose)

theorem comm_N_transpose_N :
    Nᵀ * N - N * Nᵀ = -K := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (congrArg Neg.neg comm_N_N_transpose)

theorem N_square : N * N = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

theorem N_transpose_square : Nᵀ * Nᵀ = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-! ### Trace form -/

/-- Explicit trace on `M₂(ℝ)`. -/
def tr (A : M2R) : ℝ := A 0 0 + A 1 1

/-- Bilinear trace pairing `⟨A,B⟩ = tr(A*B)`. -/
def traceForm (A B : M2R) : ℝ := tr (A * B)

/-- Boost generator norm under the trace form. -/
theorem traceForm_K_K : traceForm K K = 2 := by
  unfold traceForm tr
  norm_num [K_eval, Matrix.mul_apply, Fin.sum_univ_two]

/-- Nilpotent boundary is null. -/
theorem traceForm_N_N : traceForm N N = 0 := by
  unfold traceForm tr
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugate nilpotent boundary is null. -/
theorem traceForm_N_transpose_N_transpose : traceForm Nᵀ Nᵀ = 0 := by
  unfold traceForm tr
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-- Cross-pairing of opposite null boundaries. -/
theorem traceForm_N_N_transpose : traceForm N Nᵀ = 1 := by
  unfold traceForm tr
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem traceForm_N_transpose_N : traceForm Nᵀ N = 1 := by
  unfold traceForm tr
  norm_num [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-- Boost generator is orthogonal to both null boundaries. -/
theorem traceForm_K_N : traceForm K N = 0 ∧ traceForm K Nᵀ = 0 := by
  constructor
  · unfold traceForm tr
    norm_num [K_eval, N, Matrix.mul_apply, Fin.sum_univ_two]
  · unfold traceForm tr
    norm_num [K_eval, N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

end InfoGeometry.Canonical.ModularSL2R
