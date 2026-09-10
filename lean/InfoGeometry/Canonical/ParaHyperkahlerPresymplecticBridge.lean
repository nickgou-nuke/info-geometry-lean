import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.SplitQuaternionConcrete

/-!
# Para-Hyperkähler Presymplectic & Souriau Lie Invariance Bridge

This module formalizes the canonical mathematical synthesis connecting:
1. **Canonical Symplectic Substrate on ℝ²**:
   The standard volume / symplectic 2-form `ω₂(u, v) = u₀ v₁ - u₁ v₀`.
2. **Split-Quaternion Endomorphism Algebra**:
   The concrete generators `I, J, K ∈ Mat₂(ℝ)` satisfying the para-quaternionic relations
   `I² = -1`, `J² = 1`, `K² = 1`, `IJ = -JI = K`, and their isomorphism with
   `InfoGeometry.Canonical.SplitQuaternionConcrete`.
3. **Infinitesimal Lie Derivative & Souriau Trace Theorem**:
   The Lie derivative / infinitesimal variation `(ℒ_A ω)(u, v) = ω(A u, v) + ω(u, A v)`.
   Fundamental Theorem: `(ℒ_A ω)(u, v) = trace(A) * ω(u, v)`.
   Rotational Souriau invariance: For every traceless generator (`trace(A) = 0`), `ℒ_A ω = 0`.
   In particular, `ℒ_I ω = 0`, `ℒ_J ω = 0`, `ℒ_K ω = 0`.
   Conformal dilatation: For pure homotheties `c • id`, `ℒ_{c • id} ω = 2c ω`.
4. **Para-Hyperkähler Metric Triplet**:
   The contraction of `ω` with `(I, J, K)` induces:
   - `Ω_I(u, v) = ω(I u, v) = u₀ v₀ + u₁ v₁` (Euclidean positive-definite metric).
   - `Ω_J(u, v) = ω(J u, v) = -(u₀ v₀ - u₁ v₁)` (Minkowski metric with signature (1, 1)).
   - `Ω_K(u, v) = ω(K u, v) = u₀ v₁ + u₁ v₀` (Hyperbolic split metric).
-/

namespace InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge

open Matrix

abbrev R2 := Fin 2 → ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-! ## 1. Canonical Symplectic Form on ℝ² -/

/-- The standard canonical symplectic form on ℝ²: `ω(u, v) = u₀ v₁ - u₁ v₀`. -/
def omega2 (u v : R2) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- `ω₂` is skew-symmetric. -/
theorem omega2_skew (u v : R2) : omega2 u v = - omega2 v u := by
  dsimp [omega2]
  ring

/-- `ω₂` vanishes on equal vectors. -/
theorem omega2_self_zero (u : R2) : omega2 u u = 0 := by
  dsimp [omega2]
  ring

/-! ## 2. Split-Quaternion Generators in Mat₂(ℝ) -/

/-- The three split-quaternion generators as 2×2 real matrices. -/
def I_mat : Mat2 := !![0, 1; -1, 0]
def J_mat : Mat2 := !![0, 1; 1, 0]
def K_mat : Mat2 := !![1, 0; 0, -1]

/-- Split-quaternion basis elements from `SplitQuaternionConcrete`. -/
def i_split : SplitQuaternion := ⟨0, 1, 0, 0⟩
def j_split : SplitQuaternion := ⟨0, 0, 1, 0⟩
def k_split : SplitQuaternion := ⟨0, 0, 0, 1⟩

/-- `I_mat` is the matrix image of the basis element `i_split`. -/
theorem toMatrix_i_split : toMatrix i_split = I_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toMatrix, i_split, I_mat]

/-- `J_mat` is the matrix image of the basis element `j_split`. -/
theorem toMatrix_j_split : toMatrix j_split = J_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toMatrix, j_split, J_mat]

/-- `K_mat` is the matrix image of the basis element `k_split`. -/
theorem toMatrix_k_split : toMatrix k_split = K_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toMatrix, k_split, K_mat]

/-- `I² = -1`. -/
theorem I_sq : I_mat * I_mat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `J² = 1`. -/
theorem J_sq : J_mat * J_mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `K² = 1`. -/
theorem K_sq : K_mat * K_mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `I J = K`. -/
theorem I_mul_J : I_mat * J_mat = K_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I_mat, J_mat, K_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `J I = -K`. -/
theorem J_mul_I : J_mat * I_mat = -K_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I_mat, J_mat, K_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `J K = -I`. -/
theorem J_mul_K : J_mat * K_mat = -I_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I_mat, J_mat, K_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `K I = J`. -/
theorem K_mul_I : K_mat * I_mat = J_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I_mat, J_mat, K_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Lie algebra commutator: `[I, J] = 2K`. -/
theorem comm_I_J : I_mat * J_mat - J_mat * I_mat = 2 • K_mat := by
  rw [I_mul_J, J_mul_I]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- Lie algebra commutator: `[J, K] = -2I`. -/
theorem comm_J_K : J_mat * K_mat - K_mat * J_mat = -2 • I_mat := by
  rw [J_mul_K]
  have hKI : K_mat * J_mat = I_mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [I_mat, J_mat, K_mat, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hKI]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- Lie algebra commutator: `[K, I] = 2J`. -/
theorem comm_K_I : K_mat * I_mat - I_mat * K_mat = 2 • J_mat := by
  rw [K_mul_I]
  have hIK : I_mat * K_mat = -J_mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [I_mat, J_mat, K_mat, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hIK]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- Tracelessness of `I`. -/
theorem trace_I : Matrix.trace I_mat = 0 := by
  dsimp [I_mat, Matrix.trace, Matrix.diag]
  simp

/-- Tracelessness of `J`. -/
theorem trace_J : Matrix.trace J_mat = 0 := by
  dsimp [J_mat, Matrix.trace, Matrix.diag]
  simp

/-- Tracelessness of `K`. -/
theorem trace_K : Matrix.trace K_mat = 0 := by
  dsimp [K_mat, Matrix.trace, Matrix.diag]
  simp

/-! ## 3. Souriau Lie Derivative & Invariance Theorem -/

/-- Infinitesimal variation of the symplectic form under matrix action:
    `(ℒ_A ω)(u, v) = ω(A u, v) + ω(u, A v)`. -/
def lieDerivOmega (A : Mat2) (u v : R2) : ℝ :=
  omega2 (A.mulVec u) v + omega2 u (A.mulVec v)

/-- Fundamental Theorem: Infinitesimal variation of the symplectic form equals `trace(A) * ω(u, v)`. -/
theorem lieDerivOmega_eq_trace (A : Mat2) (u v : R2) :
    lieDerivOmega A u v = Matrix.trace A * omega2 u v := by
  dsimp [lieDerivOmega, omega2, Matrix.mulVec, dotProduct, Matrix.trace, Matrix.diag]
  simp only [Fin.sum_univ_two]
  ring

/-- Invariance under `I`: `(ℒ_I ω)(u, v) = 0`. -/
theorem lieDeriv_I_omega (u v : R2) : lieDerivOmega I_mat u v = 0 := by
  rw [lieDerivOmega_eq_trace, trace_I, zero_mul]

/-- Invariance under `J`: `(ℒ_J ω)(u, v) = 0`. -/
theorem lieDeriv_J_omega (u v : R2) : lieDerivOmega J_mat u v = 0 := by
  rw [lieDerivOmega_eq_trace, trace_J, zero_mul]

/-- Invariance under `K`: `(ℒ_K ω)(u, v) = 0`. -/
theorem lieDeriv_K_omega (u v : R2) : lieDerivOmega K_mat u v = 0 := by
  rw [lieDerivOmega_eq_trace, trace_K, zero_mul]

/-- For any traceless matrix (rotational Souriau motion), the symplectic form is invariant. -/
theorem lieDeriv_traceless_omega (A : Mat2) (hA : Matrix.trace A = 0) (u v : R2) :
    lieDerivOmega A u v = 0 := by
  rw [lieDerivOmega_eq_trace, hA, zero_mul]

/-- For any pure homothety `c • 1`, the symplectic form scales by `2c`. -/
theorem lieDeriv_homothety_omega (c : ℝ) (u v : R2) :
    lieDerivOmega (c • (1 : Mat2)) u v = 2 * c * omega2 u v := by
  rw [lieDerivOmega_eq_trace]
  have ht : Matrix.trace (c • (1 : Mat2)) = 2 * c := by
    dsimp [Matrix.trace, Matrix.diag]
    simp
  rw [ht]

/-! ## 4. The Associated Triplet of Bilinear Forms -/

/-- The form associated with `I`: `Ω_I(u, v) = ω(I u, v)`. -/
def omegaI (u v : R2) : ℝ :=
  omega2 (I_mat.mulVec u) v

/-- The form associated with `J`: `Ω_J(u, v) = ω(J u, v)`. -/
def omegaJ (u v : R2) : ℝ :=
  omega2 (J_mat.mulVec u) v

/-- The form associated with `K`: `Ω_K(u, v) = ω(K u, v)`. -/
def omegaK (u v : R2) : ℝ :=
  omega2 (K_mat.mulVec u) v

/-- Explicit expression: `Ω_I(u, v) = u₀ v₀ + u₁ v₁` (Euclidean metric). -/
theorem omegaI_eq_dot (u v : R2) : omegaI u v = u 0 * v 0 + u 1 * v 1 := by
  dsimp [omegaI, omega2, I_mat, Matrix.mulVec, dotProduct]
  simp [Fin.sum_univ_two]
  ring

/-- Explicit expression: `Ω_J(u, v) = -(u₀ v₀ - u₁ v₁)` (Minkowski metric). -/
theorem omegaJ_eq_minkowski (u v : R2) : omegaJ u v = -(u 0 * v 0 - u 1 * v 1) := by
  dsimp [omegaJ, omega2, J_mat, Matrix.mulVec, dotProduct]
  simp [Fin.sum_univ_two]

/-- Explicit expression: `Ω_K(u, v) = u₀ v₁ + u₁ v₀` (split off-diagonal metric). -/
theorem omegaK_eq_split (u v : R2) : omegaK u v = u 0 * v 1 + u 1 * v 0 := by
  dsimp [omegaK, omega2, K_mat, Matrix.mulVec, dotProduct]
  simp [Fin.sum_univ_two]

/-! ## 5. Certified Structural Synthesis Package -/

/-- Certified structural synthesis package for Para-Hyperkähler Presymplectic geometry. -/
structure ParaHyperkahlerPresymplecticSynthesis where
  i_sq_neg_one : I_mat * I_mat = -1
  j_sq_one : J_mat * J_mat = 1
  k_sq_one : K_mat * K_mat = 1
  to_matrix_i : toMatrix i_split = I_mat
  to_matrix_j : toMatrix j_split = J_mat
  to_matrix_k : toMatrix k_split = K_mat
  lie_deriv_eq_trace : ∀ (A : Mat2) (u v : R2), lieDerivOmega A u v = Matrix.trace A * omega2 u v
  lie_deriv_i_zero : ∀ (u v : R2), lieDerivOmega I_mat u v = 0
  lie_deriv_j_zero : ∀ (u v : R2), lieDerivOmega J_mat u v = 0
  lie_deriv_k_zero : ∀ (u v : R2), lieDerivOmega K_mat u v = 0
  lie_deriv_traceless_zero : ∀ (A : Mat2), Matrix.trace A = 0 → ∀ (u v : R2), lieDerivOmega A u v = 0
  lie_deriv_homothety_scale : ∀ (c : ℝ) (u v : R2), lieDerivOmega (c • (1 : Mat2)) u v = 2 * c * omega2 u v
  omega_i_is_euclidean : ∀ (u v : R2), omegaI u v = u 0 * v 0 + u 1 * v 1
  omega_j_is_minkowski : ∀ (u v : R2), omegaJ u v = -(u 0 * v 0 - u 1 * v 1)
  omega_k_is_split : ∀ (u v : R2), omegaK u v = u 0 * v 1 + u 1 * v 0

/-- The verified canonical synthesis instance. -/
def parahyperkahler_presymplectic_synthesis : ParaHyperkahlerPresymplecticSynthesis where
  i_sq_neg_one := I_sq
  j_sq_one := J_sq
  k_sq_one := K_sq
  to_matrix_i := toMatrix_i_split
  to_matrix_j := toMatrix_j_split
  to_matrix_k := toMatrix_k_split
  lie_deriv_eq_trace := lieDerivOmega_eq_trace
  lie_deriv_i_zero := lieDeriv_I_omega
  lie_deriv_j_zero := lieDeriv_J_omega
  lie_deriv_k_zero := lieDeriv_K_omega
  lie_deriv_traceless_zero := lieDeriv_traceless_omega
  lie_deriv_homothety_scale := lieDeriv_homothety_omega
  omega_i_is_euclidean := omegaI_eq_dot
  omega_j_is_minkowski := omegaJ_eq_minkowski
  omega_k_is_split := omegaK_eq_split

end InfoGeometry.Canonical.ParaHyperkahlerPresymplecticBridge
