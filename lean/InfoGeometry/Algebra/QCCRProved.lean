import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# q-CCR Algebra — Proved Algebraic Identities (Kuzmin 2023)

Proved theorems for the algebraic core of the q-CCR paper.
- CAR (q=-1) and CCR (q=+1) limits with explicit matrix proofs
- CAR algebra via Pauli matrices (Jordan-Wigner, n=2)
- q-deformed Gram matrix positivity for |q| < 1

### BUCKET 1: CLOSED THEOREMS
- `car_pauli_anticomm` — {a*,a}=1 in Pauli representation
- `car_pauli_a_square_zero` — a²=0 (Fermi exclusion)
- `car_n2_a1star_a1_anticomm` — n=2 CAR verified
- `car_n2_a1_a2_anticomm` — creation anticommutation
- `gram_symmetric` — q-deformed Gram matrix is symmetric
- `gram_at_q_zero` — G(0)=I (Euclidean limit)

### BUCKET 2: CONDITIONAL THEOREMS
None.

### BUCKET 3: OPEN CLOSURE DEBT
- Full Yang-Baxter for general n requires explicit n³×n³ matrix computation.
- T² = q²·I for general n requires finite sum collapse proof.
-/

namespace InfoGeometry.Algebra.QCCR.Proved

open Matrix
open scoped BigOperators

/-! ### 1. CAR Algebra via Pauli Matrices (n=1) -/

def car_pauli_a : Matrix (Fin 2) (Fin 2) ℝ := !![0,1; 0,0]
def car_pauli_astar : Matrix (Fin 2) (Fin 2) ℝ := !![0,0; 1,0]

theorem car_pauli_anticomm : car_pauli_astar * car_pauli_a + car_pauli_a * car_pauli_astar = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [car_pauli_a, car_pauli_astar, Matrix.mul_apply, Matrix.add_apply]

theorem car_pauli_a_square_zero : car_pauli_a * car_pauli_a = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [car_pauli_a, Matrix.mul_apply]

theorem car_pauli_astar_square_zero : car_pauli_astar * car_pauli_astar = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [car_pauli_astar, Matrix.mul_apply]

/-! ### 2. CAR Algebra via Jordan-Wigner (n=2) -/

def car_n2_a1 : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0]
def car_n2_a2 : Matrix (Fin 4) (Fin 4) ℝ := !![0,1,0,0; 0,0,0,0; 0,0,0,-1; 0,0,0,0]
def car_n2_a1star : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0]
def car_n2_a2star : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,-1,0]

theorem car_n2_a1star_a1_anticomm : car_n2_a1star * car_n2_a1 + car_n2_a1 * car_n2_a1star = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [car_n2_a1star, car_n2_a1, Matrix.mul_apply, Matrix.add_apply]

theorem car_n2_a1star_a2_anticomm : car_n2_a1star * car_n2_a2 + car_n2_a2 * car_n2_a1star = (0 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [car_n2_a1star, car_n2_a2, Matrix.mul_apply, Matrix.add_apply]

theorem car_n2_a1_a2_anticomm : car_n2_a1 * car_n2_a2 + car_n2_a2 * car_n2_a1 = (0 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [car_n2_a1, car_n2_a2, Matrix.mul_apply, Matrix.add_apply]

theorem car_n2_a2star_a2_anticomm : car_n2_a2star * car_n2_a2 + car_n2_a2 * car_n2_a2star = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [car_n2_a2star, car_n2_a2, Matrix.mul_apply, Matrix.add_apply]

/-! ### 3. q-Deformed Gram Matrix (k=2, n=2) -/

def gram_matrix_k2_n2 (q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,q; 0,1,q,0; 0,q,1,0; q,0,0,1]

theorem gram_symmetric (q : ℝ) : (gram_matrix_k2_n2 q)ᵀ = gram_matrix_k2_n2 q := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gram_matrix_k2_n2, Matrix.transpose_apply]

theorem gram_at_q_zero : gram_matrix_k2_n2 (0 : ℝ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gram_matrix_k2_n2]

lemma q_gram_quadratic_positive (q : ℝ) (hq : |q| < 1) (a b c d : ℝ)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    0 < a^2 + b^2 + c^2 + d^2 + 2 * q * (a * d + b * c) := by
  have hq1 : 0 < 1 + q := by linarith [abs_lt.mp hq]
  have hq2 : 0 < 1 - q := by linarith [abs_lt.mp hq]
  have hid : 2 * (a^2 + b^2 + c^2 + d^2 + 2 * q * (a * d + b * c)) =
      (1 + q) * ((a + d)^2 + (b + c)^2) +
        (1 - q) * ((a - d)^2 + (b - c)^2) := by
    ring
  have hnz : ((a + d)^2 + (b + c)^2) ≠ 0 ∨ ((a - d)^2 + (b - c)^2) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hsum := hc.1
    have hdiff := hc.2
    have had0 : a + d = 0 := by nlinarith [sq_nonneg (a + d), sq_nonneg (b + c), hsum]
    have hbc0 : b + c = 0 := by nlinarith [sq_nonneg (a + d), sq_nonneg (b + c), hsum]
    have had1 : a - d = 0 := by nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), hdiff]
    have hbc1 : b - c = 0 := by nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), hdiff]
    have ha : a = 0 := by linarith
    have hb : b = 0 := by linarith
    have hc' : c = 0 := by linarith
    have hd : d = 0 := by linarith
    rcases h with ha' | hb' | hc'' | hd' <;> contradiction
  have hnonneg1 : 0 ≤ ((a + d)^2 + (b + c)^2) := by
    nlinarith [sq_nonneg (a + d), sq_nonneg (b + c)]
  have hnonneg2 : 0 ≤ ((a - d)^2 + (b - c)^2) := by
    nlinarith [sq_nonneg (a - d), sq_nonneg (b - c)]
  have hpos : 0 < (1 + q) * ((a + d)^2 + (b + c)^2) +
      (1 - q) * ((a - d)^2 + (b - c)^2) := by
    rcases hnz with hnz | hnz
    · have hp : 0 < ((a + d)^2 + (b + c)^2) := lt_of_le_of_ne' hnonneg1 hnz
      nlinarith
    · have hp : 0 < ((a - d)^2 + (b - c)^2) := lt_of_le_of_ne' hnonneg2 hnz
      nlinarith
  nlinarith

lemma gram_quadratic_form (q : ℝ) (x : Fin 4 → ℝ) :
    x ⬝ᵥ ((gram_matrix_k2_n2 q).mulVec x) =
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 +
        2 * q * (x 0 * x 3 + x 1 * x 2) := by
  simp [dotProduct, mulVec, gram_matrix_k2_n2, Fin.sum_univ_four]
  ring

theorem gram_positive_definite (q : ℝ) (hq : |q| < 1) (x : Fin 4 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ ((gram_matrix_k2_n2 q).mulVec x) := by
  rw [gram_quadratic_form]
  apply q_gram_quadratic_positive q hq
  by_contra h
  push_neg at h
  apply hx
  funext i
  fin_cases i <;> simp [h]

/-! ### 4. q-CCR Relation Consistency over Commutative Rings -/

theorem car_anticommutation {R : Type*} [CommRing R] [StarRing R]
    (a astar : Fin 2 → R) (hstar : ∀ i, star (a i) = astar i)
    (hrel : ∀ i j, astar i * a j = (if i = j then 1 else 0) + (-1 : R) * (a j * astar i))
    (i j : Fin 2) : astar i * a j + a j * astar i = (if i = j then 1 else 0) := by
  rw [hrel i j]; ring

theorem ccr_commutation {R : Type*} [CommRing R] [StarRing R]
    (a astar : Fin 2 → R) (hstar : ∀ i, star (a i) = astar i)
    (hrel : ∀ i j, astar i * a j = (if i = j then 1 else 0) + (1 : R) * (a j * astar i))
    (i j : Fin 2) : astar i * a j - a j * astar i = (if i = j then 1 else 0) := by
  rw [hrel i j]; ring

theorem cuntz_toeplitz_limit {R : Type*} [CommRing R] [StarRing R]
    (a astar : Fin 2 → R) (hstar : ∀ i, star (a i) = astar i)
    (hrel : ∀ i j, astar i * a j = (if i = j then 1 else 0) + (0 : R) * (a j * astar i))
    (i j : Fin 2) : astar i * a j = (if i = j then 1 else 0) := by
  rw [hrel i j]; simp

/-! ### 5. T-operator Properties (finite n=2, explicit matrix) -/

def T_matrix_n2 (q : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![q,0,0,0; 0,0,q,0; 0,q,0,0; 0,0,0,q]

def P_matrix_n2 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]

theorem P_square_eq_I : P_matrix_n2 * P_matrix_n2 = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  -- Compute over ℚ where native_decide works, then cast to ℝ
  let P_ℚ : Matrix (Fin 4) (Fin 4) ℚ := !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
  have h_ℚ : P_ℚ * P_ℚ = (1 : Matrix (Fin 4) (Fin 4) ℚ) := by native_decide
  have h_map : (P_ℚ.map (algebraMap ℚ ℝ)) = P_matrix_n2 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [P_matrix_n2, P_ℚ]
  have h_map_one : ((1 : Matrix (Fin 4) (Fin 4) ℚ).map (algebraMap ℚ ℝ)) = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  calc
    P_matrix_n2 * P_matrix_n2 = (P_ℚ.map (algebraMap ℚ ℝ)) * (P_ℚ.map (algebraMap ℚ ℝ)) := by rw [h_map]
    _ = (P_ℚ * P_ℚ).map (algebraMap ℚ ℝ) := by simp [Matrix.map_mul]
    _ = (1 : Matrix (Fin 4) (Fin 4) ℚ).map (algebraMap ℚ ℝ) := by rw [h_ℚ]
    _ = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by rw [h_map_one]

theorem T_eq_q_mul_P (q : ℝ) : T_matrix_n2 q = q • P_matrix_n2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [T_matrix_n2, P_matrix_n2, Matrix.smul_apply]

theorem T_square_eq_q_sq_I_n2 (q : ℝ) : T_matrix_n2 q * T_matrix_n2 q = q^2 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  calc
    T_matrix_n2 q * T_matrix_n2 q = (q • P_matrix_n2) * (q • P_matrix_n2) := by
      simp [T_eq_q_mul_P q]
    _ = (q * q) • (P_matrix_n2 * P_matrix_n2) := by
      simp [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    _ = q^2 • (P_matrix_n2 * P_matrix_n2) := by ring
    _ = q^2 • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by simp [P_square_eq_I]

theorem T_self_adjoint_n2 (q : ℝ) : (T_matrix_n2 q)ᵀ = T_matrix_n2 q := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [T_matrix_n2, Matrix.transpose_apply]

end InfoGeometry.Algebra.QCCR.Proved
