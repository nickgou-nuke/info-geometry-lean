import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Cl(1,1) Split-Quaternions, Chiral Volume Form, and Nilpotents
Target: `InfoGeometry/Clifford/Cl11SplitQuaternions.lean`

Formalizes:
1. Cl(1,1) real matrix representation:
   e₁ = ((1, 0), (0, -1))   [e₁² = +1]
   e₂ = ((0, -1), (1,  0))   [e₂² = -1]
2. Anticommutation: {e₁, e₂} = 0.
3. Cockle Split-Quaternions:
   i = e₂, j = e₁, k = e₂ e₁  ⟶  i² = -1, j² = 1, k² = 1, i j k = 1.
4. Chiral Volume Form:
   ω = e₁ e₂  ⟶  ω² = +1, {ω, e₁} = 0, {ω, e₂} = 0.
5. Chiral Projectors:
   P₊ = (1 + ω)/2, P₋ = (1 - ω)/2  ⟶  P₊² = P₊, P₊ P₋ = 0, P₊ + P₋ = 1.
6. Nilpotent Lightcone Vectors:
   n₊ = e₁ + e₂  ⟶  n₊² = 0, n₋ = e₁ - e₂  ⟶  n₋² = 0.
   e₁ P₊ = (e₁ + e₂)/2 = n₊ / 2, e₁ P₋ = (e₁ - e₂)/2 = n₋ / 2.
7. Internal Geometric Complexification via Cl(1,2):
   Central 3D pseudoscalar I₃D = e₁ e₂ f with I₃D² = -1, [I₃D, X] = 0,
   yielding biquaternions 𝔹 ≅ Cl(1,2) ≅ M₂(ℂ).

All proofs compile natively with 0 sorry.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11

open scoped Matrix

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ### 1. Basis Generators -/

/-- Spacelike generator e₁ with e₁² = +1. -/
def e₁ : Mat2R :=
  !![1,  0;
     0, -1]

/-- Timelike generator e₂ with e₂² = -1 (Elliptic/Complex unit). -/
def e₂ : Mat2R :=
  !![0, -1;
     1,  0]

@[simp]
theorem e₁_sq : e₁ * e₁ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem e₂_sq : e₂ * e₂ = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₂, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem e₁_anticomm_e₂ : e₁ * e₂ + e₂ * e₁ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.add_apply]

/-! ### 2. The Cockle Split-Quaternion Isomorphism -/

def i_quat : Mat2R := e₂
def j_quat : Mat2R := e₁
def k_quat : Mat2R := e₂ * e₁

@[simp]
theorem i_sq : i_quat * i_quat = -1 := e₂_sq

@[simp]
theorem j_sq : j_quat * j_quat = 1 := e₁_sq

@[simp]
theorem k_sq : k_quat * k_quat = 1 := by
  dsimp [k_quat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem i_mul_j : i_quat * j_quat = k_quat := rfl

theorem j_mul_i : j_quat * i_quat = - k_quat := by
  dsimp [i_quat, j_quat, k_quat]
  have h := e₁_anticomm_e₂
  rw [add_eq_zero_iff_eq_neg] at h
  exact h

theorem i_j_k_prod : i_quat * j_quat * k_quat = 1 := by
  dsimp [i_quat, j_quat, k_quat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### 3. The Chiral Volume Form (Pseudoscalar) -/

/-- The volume element ω = e₁ e₂. -/
def omega : Mat2R := e₁ * e₂

/-- The volume form squares to +1 (Hyperbolic/Chiral grading). -/
@[simp]
theorem omega_sq : omega * omega = 1 := by
  dsimp [omega]
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- ω anticommutes with the spacelike vector e₁. -/
theorem omega_anticomm_e₁ : omega * e₁ + e₁ * omega = 0 := by
  dsimp [omega]
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.add_apply]

/-- ω anticommutes with the timelike vector e₂. -/
theorem omega_anticomm_e₂ : omega * e₂ + e₂ * omega = 0 := by
  dsimp [omega]
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.add_apply]

/-! ### 4. Chiral Projectors -/

def P_plus : Mat2R := (1 / 2 : ℝ) • (1 + omega)
def P_minus : Mat2R := (1 / 2 : ℝ) • (1 - omega)

@[simp]
theorem P_plus_sq : P_plus * P_plus = P_plus := by
  dsimp [P_plus]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [omega, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)

@[simp]
theorem P_minus_sq : P_minus * P_minus = P_minus := by
  dsimp [P_minus]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [omega, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)

theorem P_plus_mul_P_minus : P_plus * P_minus = 0 := by
  dsimp [P_plus, P_minus]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [omega, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)

theorem P_minus_mul_P_plus : P_minus * P_plus = 0 := by
  dsimp [P_plus, P_minus]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [omega, e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)

theorem P_plus_add_P_minus : P_plus + P_minus = 1 := by
  dsimp [P_plus, P_minus]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [omega, e₁, e₂]; try ring)

/-! ### 5. Nilpotent Lightcone Rays & Projector Action -/

/-- Lightcone generator n₊ = e₁ + e₂. -/
def n_plus : Mat2R := e₁ + e₂

/-- Lightcone generator n₋ = e₁ - e₂. -/
def n_minus : Mat2R := e₁ - e₂

/-- The lightcone vector is strictly nilpotent: n₊² = 0. -/
@[simp]
theorem n_plus_sq : n_plus * n_plus = 0 := by
  dsimp [n_plus]
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- The dual lightcone vector is strictly nilpotent: n₋² = 0. -/
@[simp]
theorem n_minus_sq : n_minus * n_minus = 0 := by
  dsimp [n_minus]
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- Projector action: e₁ P₊ = (e₁ + e₂)/2 = n₊ / 2. -/
theorem e₁_mul_P_plus : e₁ * P_plus = (1 / 2 : ℝ) • n_plus := by
  dsimp [P_plus, n_plus, omega]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-- Projector action: e₁ P₋ = (e₁ - e₂)/2 = n₋ / 2. -/
theorem e₁_mul_P_minus : e₁ * P_minus = (1 / 2 : ℝ) • n_minus := by
  dsimp [P_minus, n_minus, omega]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-- Product of nilpotent null vectors yields 4 • P₋. -/
theorem n_plus_mul_n_minus : n_plus * n_minus = (4 : ℝ) • P_minus := by
  dsimp [n_plus, n_minus, P_minus, omega]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-- Product of nilpotent null vectors yields 4 • P₊. -/
theorem n_minus_mul_n_plus : n_minus * n_plus = (4 : ℝ) • P_plus := by
  dsimp [n_plus, n_minus, P_plus, omega]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [e₁, e₂, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

theorem n_anticomm : n_plus * n_minus + n_minus * n_plus = (4 : ℝ) • (1 : Mat2R) := by
  rw [n_plus_mul_n_minus, n_minus_mul_n_plus]
  rw [← smul_add, add_comm, P_plus_add_P_minus]

/-! ### 6. Internal Geometric Complexification via Cl(1,2) Central Pseudoscalar -/

/-- Complex generator e₁ in M₂(ℂ). -/
def e₁C : Mat2C := !![1, 0; 0, -1]

/-- Complex generator e₂ in M₂(ℂ). -/
def e₂C : Mat2C := !![0, -1; 1, 0]

/-- Extra timelike generator f in M₂(ℂ) orthogonal to the plane. -/
def fC : Mat2C := !![0, Complex.I; Complex.I, 0]

@[simp] theorem e₁C_sq : e₁C * e₁C = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁C, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem e₂C_sq : e₂C * e₂C = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₂C, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

@[simp] theorem fC_sq : fC * fC = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [fC, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.neg_apply]

theorem e₁C_anticomm_e₂C : e₁C * e₂C + e₂C * e₁C = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁C, e₂C, Matrix.add_apply]

theorem e₁C_anticomm_fC : e₁C * fC + fC * e₁C = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₁C, fC, Matrix.add_apply]

theorem e₂C_anticomm_fC : e₂C * fC + fC * e₂C = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e₂C, fC, Matrix.add_apply]

/-- The 3D central volume pseudoscalar I₃D = e₁ e₂ f. -/
def I_3D : Mat2C := e₁C * e₂C * fC

theorem I_3D_eq_imaginary : I_3D = -Complex.I • (1 : Mat2C) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [I_3D, e₁C, e₂C, fC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

@[simp] theorem I_3D_sq : I_3D * I_3D = -1 := by
  rw [I_3D_eq_imaginary]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.neg_apply]

/-- Centrality of I₃D: commutes with all 2×2 complex matrices. -/
theorem I_3D_comm (M : Mat2C) : I_3D * M = M * I_3D := by
  rw [I_3D_eq_imaginary]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

/--
Theorem: Cl(1,2) Internal Complexification Matrix Generator Relations.
The 3D volume form I₃D provides a central, coordinate-free geometric imaginary unit
squaring to -1, with generators e₁C, e₂C, fC satisfying the Cl(1,2) relations.
-/
theorem cl12_biquaternion_generator_relations :
    I_3D * I_3D = -1 ∧
    (∀ M : Mat2C, I_3D * M = M * I_3D) ∧
    e₁C * e₁C = 1 ∧
    e₂C * e₂C = -1 ∧
    fC * fC = -1 :=
  ⟨I_3D_sq, I_3D_comm, e₁C_sq, e₂C_sq, fC_sq⟩

end InfoGeometry.Clifford.Cl11
