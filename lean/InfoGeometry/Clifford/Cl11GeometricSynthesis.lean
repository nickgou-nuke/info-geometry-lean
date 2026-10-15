import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Geometric Synthesis of Cl(1,1), Split-Quaternions, Subalgebras, and Cl(1,2) Complexification

This module formalizes the geometric structures of the real Clifford algebra Cl(1,1):
1. The real matrix model M₂(ℝ) with generators e₁, e₂ satisfying e₁² = 1, e₂² = -1, {e₁, e₂} = 0.
2. The canonical identification with Cockle's split-quaternions ℍ_split ≅ M₂(ℝ)
   with generators i, j, k satisfying i² = -1, j² = 1, k² = 1, ij = -k = -ji.
3. The three planar commutative subalgebras:
   - Elliptic (Complex numbers ℂ): {1, i} with i² = -1.
   - Hyperbolic (Split-complex numbers 𝔻): {1, j} with j² = +1.
   - Parabolic (Dual numbers ℝ[ε]/(ε²)): {1, ε} with ε² = 0.
4. The volume form (pseudoscalar) ω = e₁e₂:
   - ω² = 1.
   - Chiral grading: {ω, e₁} = 0, {ω, e₂} = 0.
5. The chiral idempotent projectors P± = (1 ± ω)/2:
   - P₊² = P₊, P₋² = P₋, P₊P₋ = 0, P₊ + P₋ = 1.
6. The nilpotent lightcone rays n± = e₁ ± e₂:
   - n₊² = 0, n₋² = 0.
   - n₊n₋ = 4 P₋, n₋n₊ = 4 P₊.
7. Internal geometric complexification via Cl(1,2):
   - In Cl(1,1), ω anticommutes with vectors and is not central.
   - Extending to Cl(1,2) with generators e₁, e₂, f (where f² = -1) yields
     the central 3D pseudoscalar I₃D = e₁e₂f.
   - I₃D² = -1 and I₃D commutes with all generators: [I₃D, X] = 0.
   - This provides the intrinsic geometric imaginary unit for biquaternions 𝔹 ≅ M₂(ℂ).

All proofs are verified natively by the Lean 4 kernel with 0 sorry.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11GeometricSynthesis

open scoped Matrix

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-! ## I. Native Matrix Model of Cl(1,1) -/

/-- Identity matrix in M₂(ℝ). -/
def one : Mat2R := !![1, 0; 0, 1]

lemma one_eq_one_matrix : one = (1 : Mat2R) := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Timelike / positive generator e₁: e₁² = +1. -/
def e1 : Mat2R := !![1, 0; 0, -1]

/-- Spacelike / negative generator e₂: e₂² = -1. -/
def e2 : Mat2R := !![0, 1; -1, 0]

/-- Volume form (pseudoscalar) ω = e₁e₂. -/
def omega : Mat2R := !![0, 1; 1, 0]

@[simp] theorem e1_sq : e1 * e1 = one := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e1, one, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem e2_sq : e2 * e2 = -one := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e2, one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

@[simp] theorem omega_sq : omega * omega = one := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [omega, one, Matrix.mul_apply, Fin.sum_univ_two]

theorem e1_mul_e2 : e1 * e2 = omega := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [e1, e2, omega, Matrix.mul_apply, Fin.sum_univ_two]

theorem e2_mul_e1 : e2 * e1 = -omega := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e1, e2, omega, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem e1_e2_anticomm : e1 * e2 + e2 * e1 = 0 := by
  rw [e1_mul_e2, e2_mul_e1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply]

/-! ## II. Chiral Grading Operator and Projectors -/

theorem omega_e1_anticomm : omega * e1 + e1 * omega = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [omega, e1, Matrix.add_apply]

theorem omega_e2_anticomm : omega * e2 + e2 * omega = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [omega, e2, Matrix.add_apply]

/-- Chiral projector onto the positive sheet: P₊ = (1 + ω)/2. -/
def P_plus : Mat2R := (1 / 2 : ℝ) • (one + omega)

/-- Chiral projector onto the negative sheet: P₋ = (1 - ω)/2. -/
def P_minus : Mat2R := (1 / 2 : ℝ) • (one - omega)

theorem P_plus_explicit : P_plus = !![(1/2 : ℝ), 1/2; 1/2, 1/2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_plus, one, omega]

theorem P_minus_explicit : P_minus = !![(1/2 : ℝ), -1/2; -1/2, 1/2] := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [P_minus, one, omega]; try norm_num)

@[simp] theorem P_plus_sq : P_plus * P_plus = P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [P_plus, one, omega, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)

@[simp] theorem P_minus_sq : P_minus * P_minus = P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [P_minus, one, omega, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)

theorem P_plus_mul_P_minus : P_plus * P_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, one, omega, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_minus_mul_P_plus : P_minus * P_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, one, omega, Matrix.mul_apply, Fin.sum_univ_two]

theorem P_plus_add_P_minus : P_plus + P_minus = one := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [P_plus, P_minus, one, omega] <;> ring

/-! ## III. Nilpotent Lightcone Rays -/

/-- Positive lightcone ray n₊ = e₁ + e₂. -/
def n_plus : Mat2R := e1 + e2

/-- Negative lightcone ray n₋ = e₁ - e₂. -/
def n_minus : Mat2R := e1 - e2

theorem n_plus_explicit : n_plus = !![1, 1; -1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [n_plus, e1, e2]

theorem n_minus_explicit : n_minus = !![1, -1; 1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [n_minus, e1, e2]

@[simp] theorem n_plus_sq : n_plus * n_plus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [n_plus, e1, e2, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem n_minus_sq : n_minus * n_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [n_minus, e1, e2, Matrix.mul_apply, Fin.sum_univ_two]

theorem n_plus_mul_n_minus : n_plus * n_minus = (4 : ℝ) • P_minus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [n_plus, n_minus, P_minus, e1, e2, one, omega, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem n_minus_mul_n_plus : n_minus * n_plus = (4 : ℝ) • P_plus := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [n_plus, n_minus, P_plus, e1, e2, one, omega, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem n_anticomm_sum : n_plus * n_minus + n_minus * n_plus = (4 : ℝ) • one := by
  rw [n_plus_mul_n_minus, n_minus_mul_n_plus]
  rw [← smul_add, add_comm, P_plus_add_P_minus]

/-! ## IV. Cockle's Split-Quaternions ℍ_split ≅ Cl(1,1) -/

/-- Cockle unit i: elliptic generator, i² = -1. -/
def i_cockle : Mat2R := -e2

/-- Cockle unit j: hyperbolic generator, j² = +1. -/
def j_cockle : Mat2R := omega

/-- Cockle unit k: hyperbolic generator, k² = +1. -/
def k_cockle : Mat2R := e1

@[simp] theorem i_cockle_sq : i_cockle * i_cockle = -one := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [i_cockle, e2, one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

@[simp] theorem j_cockle_sq : j_cockle * j_cockle = one := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [j_cockle, omega, one, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem k_cockle_sq : k_cockle * k_cockle = one := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [k_cockle, e1, one, Matrix.mul_apply, Fin.sum_univ_two]

theorem i_mul_j_cockle : i_cockle * j_cockle = -k_cockle := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [i_cockle, j_cockle, k_cockle, e1, e2, omega, Matrix.mul_apply, Fin.sum_univ_two]

theorem j_mul_i_cockle : j_cockle * i_cockle = k_cockle := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [i_cockle, j_cockle, k_cockle, e1, e2, omega, Matrix.mul_apply, Fin.sum_univ_two]

theorem j_mul_k_cockle : j_cockle * k_cockle = i_cockle := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [i_cockle, j_cockle, k_cockle, e1, e2, omega, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem k_mul_j_cockle : k_cockle * j_cockle = -i_cockle := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [i_cockle, j_cockle, k_cockle, e1, e2, omega, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem k_mul_i_cockle : k_cockle * i_cockle = -j_cockle := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [i_cockle, j_cockle, k_cockle, e1, e2, omega, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem i_mul_k_cockle : i_cockle * k_cockle = j_cockle := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [i_cockle, j_cockle, k_cockle, e1, e2, omega, Matrix.mul_apply, Fin.sum_univ_two]

theorem cockle_triad_product : i_cockle * j_cockle * k_cockle = -one := by
  rw [i_mul_j_cockle]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [k_cockle, e1, one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

/-! ## V. The Three Planar Commutative Subalgebras -/

/-- General element of the elliptic (complex) planar subalgebra: a + b • i. -/
def elliptic_elem (a b : ℝ) : Mat2R := a • one + b • i_cockle

theorem elliptic_mul (a b c d : ℝ) :
    elliptic_elem a b * elliptic_elem c d = elliptic_elem (a * c - b * d) (a * d + b * c) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [elliptic_elem, one, i_cockle, e2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- General element of the hyperbolic (split-complex) planar subalgebra: a + b • j. -/
def hyperbolic_elem (a b : ℝ) : Mat2R := a • one + b • j_cockle

theorem hyperbolic_mul (a b c d : ℝ) :
    hyperbolic_elem a b * hyperbolic_elem c d = hyperbolic_elem (a * c + b * d) (a * d + b * c) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hyperbolic_elem, one, j_cockle, omega, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Parabolic nilpotent generator: ε = (i_cockle + j_cockle) / 2. -/
def eps_parabolic : Mat2R := (1 / 2 : ℝ) • (i_cockle + j_cockle)

theorem eps_parabolic_explicit : eps_parabolic = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [eps_parabolic, i_cockle, j_cockle, e2, omega]; try ring)

@[simp] theorem eps_parabolic_sq : eps_parabolic * eps_parabolic = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [eps_parabolic, i_cockle, j_cockle, e2, omega, Matrix.mul_apply, Fin.sum_univ_two]

/-- General element of the parabolic (dual numbers) planar subalgebra: a + b • ε. -/
def parabolic_elem (a b : ℝ) : Mat2R := a • one + b • eps_parabolic

theorem parabolic_mul (a b c d : ℝ) :
    parabolic_elem a b * parabolic_elem c d = parabolic_elem (a * c) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [parabolic_elem, eps_parabolic, one, i_cockle, j_cockle, e2, omega,
           Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-! ## VI. Internal Geometric Complexification via Cl(1,2) and 3D Central Pseudoscalar -/

/-- Complex identity matrix in M₂(ℂ). -/
def oneC : Mat2C := !![1, 0; 0, 1]

lemma oneC_eq_one_matrix : oneC = (1 : Mat2C) := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Generator e₁ in M₂(ℂ): e₁² = +1. -/
def e1C : Mat2C := !![1, 0; 0, -1]

/-- Generator e₂ in M₂(ℂ): e₂² = -1. -/
def e2C : Mat2C := !![0, Complex.I; Complex.I, 0]

/-- Extra timelike generator f in M₂(ℂ): f² = -1. -/
def fC : Mat2C := !![0, 1; -1, 0]

@[simp] theorem e1C_sq : e1C * e1C = oneC := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e1C, oneC, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem e2C_sq : e2C * e2C = -oneC := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e2C, oneC, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.neg_apply]

@[simp] theorem fC_sq : fC * fC = -oneC := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [fC, oneC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply]

theorem e1C_e2C_anticomm : e1C * e2C + e2C * e1C = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e1C, e2C, Matrix.add_apply]

theorem e1C_fC_anticomm : e1C * fC + fC * e1C = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e1C, fC, Matrix.add_apply]

theorem e2C_fC_anticomm : e2C * fC + fC * e2C = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [e2C, fC, Matrix.add_apply]

/-- The 3D volume form (pseudoscalar) in Cl(1,2): I₃D = e₁ e₂ f. -/
def I_3D : Mat2C := e1C * e2C * fC

/-- I₃D is exactly the central imaginary scalar -i • 1. -/
theorem I_3D_eq_imaginary : I_3D = -Complex.I • oneC := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [I_3D, e1C, e2C, fC, oneC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

/-- The 3D pseudoscalar squares to -1: I₃D² = -1. -/
@[simp] theorem I_3D_sq : I_3D * I_3D = -oneC := by
  rw [I_3D_eq_imaginary]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oneC, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.neg_apply]

/-- Centrality of I₃D: it commutes with ANY 2x2 complex matrix. -/
theorem I_3D_comm_any (M : Mat2C) : I_3D * M = M * I_3D := by
  rw [I_3D_eq_imaginary, oneC_eq_one_matrix]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply]

/-- I₃D commutes with e₁ (centrality). -/
theorem I_3D_comm_e1C : I_3D * e1C = e1C * I_3D :=
  I_3D_comm_any e1C

/-- I₃D commutes with e₂ (centrality). -/
theorem I_3D_comm_e2C : I_3D * e2C = e2C * I_3D :=
  I_3D_comm_any e2C

/-- I₃D commutes with f (centrality). -/
theorem I_3D_comm_fC : I_3D * fC = fC * I_3D :=
  I_3D_comm_any fC

/--
Geometric Complexification Theorem:
The 3D Clifford algebra Cl(1,2) naturally embeds Cl(1,1) while providing an intrinsic
geometric central imaginary unit I₃D, realizing the biquaternions 𝔹 ≅ Cl(1,2) ≅ M₂(ℂ).
-/
theorem cl12_internal_complexification :
    I_3D * I_3D = -oneC ∧
    (∀ M : Mat2C, I_3D * M = M * I_3D) ∧
    e1C * e1C = oneC ∧
    e2C * e2C = -oneC ∧
    fC * fC = -oneC :=
  ⟨I_3D_sq, I_3D_comm_any, e1C_sq, e2C_sq, fC_sq⟩

end InfoGeometry.Clifford.Cl11GeometricSynthesis
