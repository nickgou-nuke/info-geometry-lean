import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Noncommutative Chiral Grading Operator and Lightcone Projector Algebra

This module formalizes the complete native Mathlib real 2×2 matrix representation of the
Clifford algebra `Cl(1,1)`, its chiral grading operator (volume element) `Γ`, and the
corresponding chiral lightcone projector algebra.

## Key Definitions
- `Mat2R`: Real 2×2 matrices `Matrix (Fin 2) (Fin 2) ℝ`.
- `e₁`, `e₂`: Clifford generators with `e₁² = 1`, `e₂² = -1`, and `{e₁, e₂} = 0`.
- `Γ`: The chiral grading operator `Γ = e₁ * e₂`, which is involutive (`Γ² = 1`) and
  strictly anticommutes with all 1-vectors.
- `P_plus`, `P_minus`: Chiral lightcone projectors `(1/2) • (1 ± Γ)` satisfying idempotence,
  mutual orthogonality, and completeness.
- `n_plus`, `n_minus`: Lightcone null generators `e₁ ± e₂` satisfying nilpotency and the
  null operator product algebra `n₊ * n₋ = 4 • P₋`, `n₋ * n₊ = 4 • P₊`.

## Strict Non-Vacuity
All identities are proven constructively via Mathlib matrix tactics (`ext i j`, `fin_cases`,
`simp`, `ring`, `norm_num`) with complete proofs and zero unproven gaps or axioms.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChiralLightconeProjectorAlgebra

open scoped Matrix

/-- Real 2×2 matrix carrier for the `Cl(1,1)` operator algebra. -/
abbrev Mat2R : Type := Matrix (Fin 2) (Fin 2) ℝ

/-! ## 1. Clifford Generators and Chiral Grading Operator -/

/-- Space-like generator `e₁` of `Cl(1,1)` squaring to `+1`. -/
def e₁ : Mat2R := !![(1 : ℝ), 0; 0, (-1 : ℝ)]

/-- Time-like generator `e₂` of `Cl(1,1)` squaring to `-1`. -/
def e₂ : Mat2R := !![(0 : ℝ), (-1 : ℝ); 1, 0]

/-- Chiral grading operator (volume form / pseudoscalar) `Γ = e₁ * e₂`. -/
def Γ : Mat2R := e₁ * e₂

/-- Explicit matrix form of `Γ`. -/
lemma Γ_eq_matrix : Γ = !![(0 : ℝ), -1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Γ, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 2. Fundamental Algebraic Relations of Generators -/

/-- Space-like generator squares to `1`. -/
@[simp] theorem e1_sq : e₁ * e₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₁, Matrix.mul_apply, Fin.sum_univ_two]

/-- Time-like generator squares to `-1`. -/
@[simp] theorem e2_sq : e₂ * e₂ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-- Generators strictly anticommute: `{e₁, e₂} = 0`. -/
theorem e1_anticomm_e2 : e₁ * e₂ + e₂ * e₁ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]

/-- Generators are strictly non-commutative. -/
theorem generators_noncommutative : e₁ * e₂ ≠ e₂ * e₁ := by
  intro h
  have h_entry := congr_fun (congr_fun h 0) 1
  norm_num [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two] at h_entry

/-! ## 3. Properties of the Chiral Grading Operator `Γ` -/

/-- The chiral grading operator is an involution: `Γ² = 1`. -/
@[simp] theorem gamma_sq : Γ * Γ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Γ_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Γ` strictly anticommutes with `e₁`: `{Γ, e₁} = 0`. -/
theorem gamma_anticomm_e1 : Γ * e₁ + e₁ * Γ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Γ_eq_matrix, e₁, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]

/-- `Γ` strictly anticommutes with `e₂`: `{Γ, e₂} = 0`. -/
theorem gamma_anticomm_e2 : Γ * e₂ + e₂ * Γ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Γ_eq_matrix, e₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]

/-- `Γ` strictly anticommutes with any 1-vector `v = v₁ • e₁ + v₂ • e₂`. -/
theorem gamma_anticomm_vec (v₁ v₂ : ℝ) :
    Γ * (v₁ • e₁ + v₂ • e₂) + (v₁ • e₁ + v₂ • e₂) * Γ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Γ_eq_matrix, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two,
              Matrix.add_apply, Matrix.smul_apply]

/-- Noncommutative certificate: `Γ` does not commute with `e₁`. -/
theorem chiral_grading_nontrivial : Γ * e₁ ≠ e₁ * Γ := by
  intro h
  have h_entry := congr_fun (congr_fun h 0) 1
  norm_num [Γ_eq_matrix, e₁, Matrix.mul_apply, Fin.sum_univ_two] at h_entry

/-! ## 4. Chiral Grading Action on Multivectors -/

/-- Chiral action on the identity element: `Γ * 1 * Γ = 1`. -/
@[simp] theorem chiral_action_one : Γ * (1 : Mat2R) * Γ = 1 := by
  rw [Matrix.mul_one, gamma_sq]

/-- Chiral action on the pseudoscalar: `Γ * Γ * Γ = Γ`. -/
@[simp] theorem chiral_action_gamma : Γ * Γ * Γ = Γ := by
  rw [Matrix.mul_assoc, gamma_sq, Matrix.mul_one]

/-- Chiral action on `e₁` flips sign: `Γ * e₁ * Γ = -e₁`. -/
theorem chiral_action_e1 : Γ * e₁ * Γ = -e₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Γ_eq_matrix, e₁, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-- Chiral action on `e₂` flips sign: `Γ * e₂ * Γ = -e₂`. -/
theorem chiral_action_e2 : Γ * e₂ * Γ = -e₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Γ_eq_matrix, e₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

set_option linter.unusedSimpArgs false

/-- Chiral grading action on the even (bosonic) subspace `span{1, Γ}` is invariant. -/
theorem chiral_action_even (a b : ℝ) :
    Γ * (a • (1 : Mat2R) + b • Γ) * Γ = a • (1 : Mat2R) + b • Γ := by
  calc
    Γ * (a • (1 : Mat2R) + b • Γ) * Γ
      = (Γ * (a • 1) + Γ * (b • Γ)) * Γ := by rw [Matrix.mul_add]
    _ = (a • (Γ * 1) + b • (Γ * Γ)) * Γ := by
          simp only [Matrix.mul_smul]
    _ = (a • Γ + b • 1) * Γ := by rw [Matrix.mul_one, gamma_sq]
    _ = (a • Γ) * Γ + (b • (1 : Mat2R)) * Γ := by rw [Matrix.add_mul]
    _ = a • (Γ * Γ) + b • (1 * Γ) := by
          simp only [Matrix.smul_mul]
    _ = a • 1 + b • Γ := by rw [gamma_sq, Matrix.one_mul]

/-- Chiral grading action on the odd (fermionic) subspace `span{e₁, e₂}` flips sign. -/
theorem chiral_action_odd (v₁ v₂ : ℝ) :
    Γ * (v₁ • e₁ + v₂ • e₂) * Γ = -(v₁ • e₁ + v₂ • e₂) := by
  calc
    Γ * (v₁ • e₁ + v₂ • e₂) * Γ
      = (Γ * (v₁ • e₁) + Γ * (v₂ • e₂)) * Γ := by rw [Matrix.mul_add]
    _ = (v₁ • (Γ * e₁) + v₂ • (Γ * e₂)) * Γ := by
          simp only [Matrix.mul_smul]
    _ = (v₁ • (Γ * e₁)) * Γ + (v₂ • (Γ * e₂)) * Γ := by rw [Matrix.add_mul]
    _ = v₁ • (Γ * e₁ * Γ) + v₂ • (Γ * e₂ * Γ) := by
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
    _ = v₁ • (-e₁) + v₂ • (-e₂) := by rw [chiral_action_e1, chiral_action_e2]
    _ = -(v₁ • e₁ + v₂ • e₂) := by
          simp only [smul_neg, ← neg_add]

/-! ## 5. Chiral Lightcone Projectors -/

/-- Positive chiral projector `P₊ = (1/2) • (1 + Γ)`. -/
def P_plus : Mat2R := (1 / 2 : ℝ) • (1 + Γ)

/-- Negative chiral projector `P₋ = (1/2) • (1 - Γ)`. -/
def P_minus : Mat2R := (1 / 2 : ℝ) • (1 - Γ)

/-- Explicit matrix representation of `P₊`. -/
lemma P_plus_eq_matrix : P_plus = !![(1 / 2 : ℝ), -1 / 2; -1 / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P_plus, Γ_eq_matrix, Matrix.add_apply, Matrix.smul_apply]

/-- Explicit matrix representation of `P₋`. -/
lemma P_minus_eq_matrix : P_minus = !![(1 / 2 : ℝ), 1 / 2; 1 / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P_minus, Γ_eq_matrix, Matrix.sub_apply, Matrix.smul_apply]

/-- Idempotence of positive projector: `P₊ * P₊ = P₊`. -/
@[simp] theorem P_plus_sq : P_plus * P_plus = P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P_plus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Idempotence of negative projector: `P₋ * P₋ = P₋`. -/
@[simp] theorem P_minus_sq : P_minus * P_minus = P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P_minus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Orthogonality: `P₊ * P₋ = 0`. -/
@[simp] theorem P_plus_mul_P_minus : P_plus * P_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P_plus_eq_matrix, P_minus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Orthogonality: `P₋ * P₊ = 0`. -/
@[simp] theorem P_minus_mul_P_plus : P_minus * P_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P_plus_eq_matrix, P_minus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Completeness (resolution of identity): `P₊ + P₋ = 1`. -/
@[simp] theorem P_plus_add_P_minus : P_plus + P_minus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P_plus_eq_matrix, P_minus_eq_matrix, Matrix.add_apply]

/-- Noncommutative operator certificate: `P₊` does not commute with `e₁`. -/
theorem projector_noncommutative : P_plus * e₁ ≠ e₁ * P_plus := by
  intro h
  have h_entry := congr_fun (congr_fun h 0) 1
  norm_num [P_plus_eq_matrix, e₁, Matrix.mul_apply, Fin.sum_univ_two] at h_entry

/-- Noncommutative operator certificate: `P₋` does not commute with `e₁`. -/
theorem projector_minus_noncommutative : P_minus * e₁ ≠ e₁ * P_minus := by
  intro h
  have h_entry := congr_fun (congr_fun h 0) 1
  norm_num [P_minus_eq_matrix, e₁, Matrix.mul_apply, Fin.sum_univ_two] at h_entry

/-! ## 6. Lightcone Null Vectors -/

/-- Forward lightcone null vector `n₊ = e₁ + e₂`. -/
def n_plus : Mat2R := e₁ + e₂

/-- Backward lightcone null vector `n₋ = e₁ - e₂`. -/
def n_minus : Mat2R := e₁ - e₂

/-- Explicit matrix representation of `n₊`. -/
lemma n_plus_eq_matrix : n_plus = !![(1 : ℝ), -1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_plus, e₁, e₂, Matrix.add_apply]

/-- Explicit matrix representation of `n₋`. -/
lemma n_minus_eq_matrix : n_minus = !![(1 : ℝ), 1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_minus, e₁, e₂, Matrix.sub_apply]

/-- Forward null vector is nilpotent: `n₊² = 0`. -/
@[simp] theorem n_plus_sq : n_plus * n_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_plus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Backward null vector is nilpotent: `n₋² = 0`. -/
@[simp] theorem n_minus_sq : n_minus * n_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_minus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 7. Projection into Null Eigenspaces -/

/-- Generator `e₁` acts on positive projector to produce half of forward null vector. -/
theorem e1_mul_P_plus : e₁ * P_plus = (1 / 2 : ℝ) • n_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₁, P_plus_eq_matrix, n_plus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- Generator `e₁` acts on negative projector to produce half of backward null vector. -/
theorem e1_mul_P_minus : e₁ * P_minus = (1 / 2 : ℝ) • n_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₁, P_minus_eq_matrix, n_minus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- Generator `e₂` acts on positive projector to produce half of forward null vector.
Note: Since `(e₁ + e₂) * P₊ = n₊ * P₊ = n₊`, `e₂ * P₊` equals `(1/2) • n₊`. -/
theorem e2_mul_P_plus : e₂ * P_plus = (1 / 2 : ℝ) • n_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₂, P_plus_eq_matrix, n_plus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- Generator `e₂` acts on negative projector to produce `-1/2` of backward null vector.
Note: Since `(e₁ - e₂) * P₋ = n₋ * P₋ = n₋`, `e₂ * P₋` equals `-(1/2) • n₋`. -/
theorem e2_mul_P_minus : e₂ * P_minus = -(1 / 2 : ℝ) • n_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₂, P_minus_eq_matrix, n_minus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.neg_apply]

/-- Right action of `e₁` on `P₊`. -/
theorem P_plus_mul_e1 : P_plus * e₁ = (1 / 2 : ℝ) • n_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₁, P_plus_eq_matrix, n_minus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- Right action of `e₁` on `P₋`. -/
theorem P_minus_mul_e1 : P_minus * e₁ = (1 / 2 : ℝ) • n_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₁, P_minus_eq_matrix, n_plus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- Right action of `e₂` on `P₊`. -/
theorem P_plus_mul_e2 : P_plus * e₂ = -(1 / 2 : ℝ) • n_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₂, P_plus_eq_matrix, n_minus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.neg_apply]

/-- Right action of `e₂` on `P₋`. -/
theorem P_minus_mul_e2 : P_minus * e₂ = (1 / 2 : ℝ) • n_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [e₂, P_minus_eq_matrix, n_plus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- Forward null vector is a right eigenvector of `P₊`: `n₊ * P₊ = n₊`. -/
@[simp] theorem n_plus_mul_P_plus : n_plus * P_plus = n_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_plus_eq_matrix, P_plus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Forward null vector is annihilated by `P₋`: `n₊ * P₋ = 0`. -/
@[simp] theorem n_plus_mul_P_minus : n_plus * P_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_plus_eq_matrix, P_minus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Backward null vector is a right eigenvector of `P₋`: `n₋ * P₋ = n₋`. -/
@[simp] theorem n_minus_mul_P_minus : n_minus * P_minus = n_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_minus_eq_matrix, P_minus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Backward null vector is annihilated by `P₊`: `n₋ * P₊ = 0`. -/
@[simp] theorem n_minus_mul_P_plus : n_minus * P_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_minus_eq_matrix, P_plus_eq_matrix, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 8. Null Operator Product and Anticommutator Algebra -/

/-- Product of forward and backward null vectors is proportional to negative projector:
`n₊ * n₋ = 4 • P₋`. -/
theorem n_plus_mul_n_minus : n_plus * n_minus = (4 : ℝ) • P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_plus_eq_matrix, n_minus_eq_matrix, P_minus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- Product of backward and forward null vectors is proportional to positive projector:
`n₋ * n₊ = 4 • P₊`. -/
theorem n_minus_mul_n_plus : n_minus * n_plus = (4 : ℝ) • P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_plus_eq_matrix, n_minus_eq_matrix, P_plus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- Null vector anticommutator resolves the identity:
`{n₊, n₋} = n₊ * n₋ + n₋ * n₊ = 4 • 1`. -/
theorem null_anticommutator : n_plus * n_minus + n_minus * n_plus = (4 : ℝ) • (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [n_plus_eq_matrix, n_minus_eq_matrix,
              Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]

end InfoGeometry.Clifford.ChiralLightconeProjectorAlgebra
