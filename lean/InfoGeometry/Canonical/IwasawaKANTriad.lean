import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace InfoGeometry.Canonical.IwasawaKANTriad

variable (R : Type*) [CommRing R]

def X_k (θ : R) : Matrix (Fin 2) (Fin 2) R := !![0, -θ; θ, 0]
def X_a (t₁ t₂ : R) : Matrix (Fin 2) (Fin 2) R := !![t₁, 0; 0, t₂]
def X_n (x : R) : Matrix (Fin 2) (Fin 2) R := !![0, x; 0, 0]

theorem X_k_trace_zero (θ : R) : Matrix.trace (X_k R θ) = 0 := by
  rw [Matrix.trace_fin_two]
  simp [X_k]
theorem X_n_trace_zero (x : R) : Matrix.trace (X_n R x) = 0 := by
  rw [Matrix.trace_fin_two]
  simp [X_n]
theorem kan_trace_localization (θ t₁ t₂ x : R) :
    Matrix.trace (X_k R θ + X_a R t₁ t₂ + X_n R x) = Matrix.trace (X_a R t₁ t₂) := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  change ((0 : R) + t₁ + 0) + ((0 : R) + t₂ + 0) = t₁ + t₂
  ring

def K_grp (c s : R) : Matrix (Fin 2) (Fin 2) R := !![c, -s; s, c]
def A_grp (t₁ t₂ : R) : Matrix (Fin 2) (Fin 2) R := !![t₁, 0; 0, t₂]
def N_grp (x : R) : Matrix (Fin 2) (Fin 2) R := !![1, x; 0, 1]

theorem N_grp_det_one (x : R) : (N_grp R x).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [N_grp]
theorem A_grp_det (t₁ t₂ : R) : (A_grp R t₁ t₂).det = t₁ * t₂ := by
  rw [Matrix.det_fin_two]
  simp [A_grp]
theorem K_grp_det (c s : R) : (K_grp R c s).det = c^2 + s^2 := by
  rw [Matrix.det_fin_two]
  simp [K_grp]
  ring
theorem kan_det_factorization (c s t₁ t₂ x : R) :
    (K_grp R c s * A_grp R t₁ t₂ * N_grp R x).det = (K_grp R c s).det * (A_grp R t₁ t₂).det * (N_grp R x).det := by
  rw [Matrix.det_mul, Matrix.det_mul]

/-- Composition of the upper unipotent factors adds their shear parameters. -/
theorem N_grp_mul (x y : R) :
    N_grp R x * N_grp R y = N_grp R (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals rw [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [N_grp] <;> ring

/-- Composition of diagonal factors is componentwise multiplication. -/
theorem A_grp_mul (t₁ t₂ u₁ u₂ : R) :
    A_grp R t₁ t₂ * A_grp R u₁ u₂ = A_grp R (t₁ * u₁) (t₂ * u₂) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals rw [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [A_grp] <;> ring

/-- The compact-factor parameters compose by the angle-addition polynomial law. -/
theorem K_grp_mul (c s c' s' : R) :
    K_grp R c s * K_grp R c' s' =
      K_grp R (c * c' - s * s') (s * c' + c * s') := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals rw [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simp [K_grp] <;> ring

/-- The product `K(c,s) A(t₁,t₂) N(x)` in explicit matrix coordinates. -/
theorem kan_product_entries (c s t₁ t₂ x : R) :
    K_grp R c s * A_grp R t₁ t₂ * N_grp R x =
      !![c * t₁, c * t₁ * x - s * t₂; s * t₁, s * t₁ * x + c * t₂] := by
  have hKA : K_grp R c s * A_grp R t₁ t₂ =
      !![c * t₁, -s * t₂; s * t₁, c * t₂] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, K_grp, A_grp] <;> ring
  rw [hKA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, N_grp] <;> ring

/-- The compact factor has determinant one when its parameters lie on the unit circle. -/
theorem K_grp_det_one_of_circle (c s : R) (h : c ^ 2 + s ^ 2 = 1) :
    (K_grp R c s).det = 1 := by
  rw [K_grp_det]
  exact h

/-- The diagonal factor has determinant one under the `SL₂` normalization. -/
theorem A_grp_det_one_of_sl2 (t₁ t₂ : R) (h : t₁ * t₂ = 1) :
    (A_grp R t₁ t₂).det = 1 := by
  rw [A_grp_det]
  exact h

def e1 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]
def e2 : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]
def eps : Matrix (Fin 2) (Fin 2) R := e2 R * e1 R

theorem e1_sq : e1 R * e1 R = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [e1] <;> ring
theorem e2_sq : e2 R * e2 R = -(1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [e2, Matrix.neg_apply] <;> ring

theorem eps_eq : eps R = !![1, 0; 0, -1] := by
  unfold eps
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, e1, e2] <;> ring

theorem eps_sq : eps R * eps R = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [eps_eq R]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def P_plus : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, 0]
def P_minus : Matrix (Fin 2) (Fin 2) R := !![0, 0; 0, 1]

theorem P_plus_def : (2 : R) • P_plus R = (1 : Matrix (Fin 2) (Fin 2) R) + eps R := by
  rw [eps_eq R]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply,
      P_plus] <;> ring
theorem P_minus_def : (2 : R) • P_minus R = (1 : Matrix (Fin 2) (Fin 2) R) - eps R := by
  rw [eps_eq R]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pi.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply,
      P_minus] <;> ring

def e_plus : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
theorem e_plus_def : (2 : R) • e_plus R = e1 R + e2 R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Pi.smul_apply, smul_eq_mul, Matrix.add_apply,
      e_plus, e1, e2] <;> ring

theorem e_plus_sq : e_plus R * e_plus R = (0 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;> simp [e_plus] <;> ring

theorem N_mediates_peirce_polarization (x : R) : N_grp R x * P_minus R = P_minus R + x • e_plus R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Pi.smul_apply, smul_eq_mul, N_grp, P_minus, e_plus] <;> ring
