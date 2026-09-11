import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# 4D Sp(4, ℝ) Para-Hyperkähler Presymplectic & Souriau Lie Invariance Bridge

This module formalizes the canonical mathematical bridge uniting:
1. **Canonical 4D Symplectic Substrate**:
   The standard Darboux symplectic form $\Omega_4(u, v) = u^T J_4 v$ on $\mathbb{R}^4$,
   where $J_4 = \begin{pmatrix} 0 & \mathbf{1}_2 \\ -\mathbf{1}_2 & 0 \end{pmatrix}$.
2. **Symplectic Lie Algebra $\mathfrak{sp}(4, \mathbb{R})$**:
   The infinitesimal symplectic condition $M^T J_4 + J_4 M = 0$ guaranteeing exact
   invariance of the symplectic form: $(\mathcal{L}_M \Omega_4)(u, v) = 0$.
3. **4D Para-Hyperkähler Triplet**:
   The canonical endomorphisms $I_4, J_4, K_4 \in \mathrm{Mat}_4(\mathbb{R})$ satisfying the
   para-quaternionic relations:
   $$I_4^2 = -\mathbf{1}_4, \quad J_4^2 = \mathbf{1}_4, \quad K_4^2 = \mathbf{1}_4,$$
   $$I_4 J_4 = -J_4 I_4 = K_4, \quad J_4 K_4 = -K_4 J_4 = -I_4, \quad K_4 I_4 = -I_4 K_4 = J_4,$$
   forming an $\mathfrak{sl}_2(\mathbb{R})$ Lie algebra under matrix commutators.
4. **Symplectic Subalgebra Embedding**:
   **Fundamental Theorem**: All three generators $I_4, J_4, K_4$ belong to $\mathfrak{sp}(4, \mathbb{R})$:
   $$I_4^T J_4 + J_4 I_4 = 0, \quad J_4^T J_4 + J_4 J_4 = 0, \quad K_4^T J_4 + J_4 K_4 = 0.$$
   Consequently, each generator generates a volume-preserving Souriau rotational symmetry of $\Omega_4$:
   $$\mathcal{L}_{I_4} \Omega_4 = 0, \quad \mathcal{L}_{J_4} \Omega_4 = 0, \quad \mathcal{L}_{K_4} \Omega_4 = 0.$$
5. **4D Metric Triplet**:
   Contraction of $\Omega_4$ with $(I_4, J_4, K_4)$ produces:
   - $\Omega_{I_4}(u, v) = \Omega_4(I_4 u, v) = u \cdot v$ (4D Euclidean positive-definite metric).
   - $\Omega_{J_4}(u, v) = \Omega_4(J_4 u, v) = -(u_0 v_0 + u_1 v_1 - u_2 v_2 - u_3 v_3)$ (neutral signature $(2, 2)$ Minkowski metric).
   - $\Omega_{K_4}(u, v) = \Omega_4(K_4 u, v) = u_0 v_2 + u_1 v_3 + u_2 v_0 + u_3 v_1$ (hyperbolic split metric).
-/

namespace InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge

open Matrix

abbrev R4 := InfoGeometry.Algebra.FiniteSpin.Vec4R
abbrev Mat4 := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-! ## 1. Canonical Symplectic Matrix and Form on ℝ⁴ -/

/-- The canonical symplectic matrix in dimension 4:
    $J_4 = \begin{pmatrix} 0 & \mathbf{1}_2 \\ -\mathbf{1}_2 & 0 \end{pmatrix}$. -/
def J4_mat : Mat4 := !![
  0,  0,  1,  0;
  0,  0,  0,  1;
 -1,  0,  0,  0;
  0, -1,  0,  0
]

/-- The canonical symplectic 2-form on $\mathbb{R}^4$: $\Omega_4(u, v) = u^T J_4 v$. -/
def omega4 (u v : R4) : ℝ :=
  u 0 * v 2 + u 1 * v 3 - u 2 * v 0 - u 3 * v 1

/-- Skew-symmetry of $\Omega_4$. -/
theorem omega4_skew (u v : R4) : omega4 u v = - omega4 v u := by
  dsimp [omega4]
  ring

/-- $\Omega_4$ vanishes on identical vectors. -/
theorem omega4_self_zero (u : R4) : omega4 u u = 0 := by
  dsimp [omega4]
  ring

/-! ## 2. The 4D Para-Hyperkähler Endomorphism Triplet -/

/-- The three 4D Para-Hyperkähler generators in $\mathrm{Mat}_4(\mathbb{R})$. -/
def I4_mat : Mat4 := J4_mat

def J4_para : Mat4 := !![
  0, 0, 1, 0;
  0, 0, 0, 1;
  1, 0, 0, 0;
  0, 1, 0, 0
]

def K4_para : Mat4 := !![
  1,  0,  0,  0;
  0,  1,  0,  0;
  0,  0, -1,  0;
  0,  0,  0, -1
]

/-- Explicit matrix-vector multiplications as simp lemmas. -/
@[simp] theorem I4_mulVec_0 (u : R4) : (I4_mat.mulVec u) 0 = u 2 := by
  simp [I4_mat, J4_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem I4_mulVec_1 (u : R4) : (I4_mat.mulVec u) 1 = u 3 := by
  simp [I4_mat, J4_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem I4_mulVec_2 (u : R4) : (I4_mat.mulVec u) 2 = -u 0 := by
  simp [I4_mat, J4_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem I4_mulVec_3 (u : R4) : (I4_mat.mulVec u) 3 = -u 1 := by
  simp [I4_mat, J4_mat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem J4_mulVec_0 (u : R4) : (J4_para.mulVec u) 0 = u 2 := by
  simp [J4_para, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem J4_mulVec_1 (u : R4) : (J4_para.mulVec u) 1 = u 3 := by
  simp [J4_para, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem J4_mulVec_2 (u : R4) : (J4_para.mulVec u) 2 = u 0 := by
  simp [J4_para, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem J4_mulVec_3 (u : R4) : (J4_para.mulVec u) 3 = u 1 := by
  simp [J4_para, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem K4_mulVec_0 (u : R4) : (K4_para.mulVec u) 0 = u 0 := by
  simp [K4_para, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem K4_mulVec_1 (u : R4) : (K4_para.mulVec u) 1 = u 1 := by
  simp [K4_para, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem K4_mulVec_2 (u : R4) : (K4_para.mulVec u) 2 = -u 2 := by
  simp [K4_para, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem K4_mulVec_3 (u : R4) : (K4_para.mulVec u) 3 = -u 3 := by
  simp [K4_para, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem smul_one_mulVec_0 (c : ℝ) (u : R4) : ((c • (1 : Mat4)).mulVec u) 0 = c * u 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem smul_one_mulVec_1 (c : ℝ) (u : R4) : ((c • (1 : Mat4)).mulVec u) 1 = c * u 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem smul_one_mulVec_2 (c : ℝ) (u : R4) : ((c • (1 : Mat4)).mulVec u) 2 = c * u 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[simp] theorem smul_one_mulVec_3 (c : ℝ) (u : R4) : ((c • (1 : Mat4)).mulVec u) 3 = c * u 3 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- $I_4^2 = -1$. -/
theorem I4_sq : I4_mat * I4_mat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I4_mat, J4_mat, Matrix.mul_apply, Fin.sum_univ_four]

/-- $J_4^2 = 1$. -/
theorem J4_sq : J4_para * J4_para = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J4_para, Matrix.mul_apply, Fin.sum_univ_four]

/-- $K_4^2 = 1$. -/
theorem K4_sq : K4_para * K4_para = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K4_para, Matrix.mul_apply, Fin.sum_univ_four]

/-- $I_4 J_4 = K_4$. -/
theorem I4_mul_J4 : I4_mat * J4_para = K4_para := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I4_mat, J4_mat, J4_para, K4_para, Matrix.mul_apply, Fin.sum_univ_four]

/-- $J_4 I_4 = -K_4$. -/
theorem J4_mul_I4 : J4_para * I4_mat = -K4_para := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I4_mat, J4_mat, J4_para, K4_para, Matrix.mul_apply, Fin.sum_univ_four]

/-- $J_4 K_4 = -I_4$. -/
theorem J4_mul_K4 : J4_para * K4_para = -I4_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I4_mat, J4_mat, J4_para, K4_para, Matrix.mul_apply, Fin.sum_univ_four]

/-- $K_4 I_4 = J_4$. -/
theorem K4_mul_I4 : K4_para * I4_mat = J4_para := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I4_mat, J4_mat, J4_para, K4_para, Matrix.mul_apply, Fin.sum_univ_four]

/-- Lie algebra commutators in $\mathrm{Mat}_4(\mathbb{R})$: $[I, J] = 2K$, $[J, K] = -2I$, $[K, I] = 2J$. -/
theorem comm_I4_J4 : I4_mat * J4_para - J4_para * I4_mat = 2 • K4_para := by
  rw [I4_mul_J4, J4_mul_I4]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

theorem comm_J4_K4 : J4_para * K4_para - K4_para * J4_para = -2 • I4_mat := by
  rw [J4_mul_K4]
  have hKI : K4_para * J4_para = I4_mat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [I4_mat, J4_mat, J4_para, K4_para, Matrix.mul_apply, Fin.sum_univ_four]
  rw [hKI]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

theorem comm_K4_I4 : K4_para * I4_mat - I4_mat * K4_para = 2 • J4_para := by
  rw [K4_mul_I4]
  have hIK : I4_mat * K4_para = -J4_para := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [I4_mat, J4_mat, J4_para, K4_para, Matrix.mul_apply, Fin.sum_univ_four]
  rw [hIK]
  ext i j
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- Tracelessness of all three 4D generators. -/
theorem trace_I4 : Matrix.trace I4_mat = 0 := by
  dsimp [I4_mat, J4_mat, Matrix.trace, Matrix.diag]
  simp [Fin.sum_univ_four]

theorem trace_J4 : Matrix.trace J4_para = 0 := by
  dsimp [J4_para, Matrix.trace, Matrix.diag]
  simp [Fin.sum_univ_four]

theorem trace_K4 : Matrix.trace K4_para = 0 := by
  dsimp [K4_para, Matrix.trace, Matrix.diag]
  simp [Fin.sum_univ_four]

/-! ## 3. Symplectic Lie Algebra 𝔰𝔭(4, ℝ) Membership -/

/-- Definition of the infinitesimal symplectic condition: $M^T J_4 + J_4 M = 0$. -/
def IsInSp4LieAlgebra (M : Mat4) : Prop :=
  Mᵀ * J4_mat + J4_mat * M = 0

/-- $I_4$ belongs to $\mathfrak{sp}(4, \mathbb{R})$. -/
theorem I4_in_sp4 : IsInSp4LieAlgebra I4_mat := by
  dsimp [IsInSp4LieAlgebra, I4_mat, J4_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]

/-- $J_4$ belongs to $\mathfrak{sp}(4, \mathbb{R})$. -/
theorem J4_in_sp4 : IsInSp4LieAlgebra J4_para := by
  dsimp [IsInSp4LieAlgebra, J4_para, J4_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]

/-- $K_4$ belongs to $\mathfrak{sp}(4, \mathbb{R})$. -/
theorem K4_in_sp4 : IsInSp4LieAlgebra K4_para := by
  dsimp [IsInSp4LieAlgebra, K4_para, J4_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]

/-! ## 4. Souriau Lie Derivative on ℝ⁴ -/

/-- Infinitesimal variation of the 4D symplectic form under matrix action:
    $(\mathcal{L}_M \Omega_4)(u, v) = \Omega_4(M u, v) + \Omega_4(u, M v)$. -/
def lieDerivOmega4 (M : Mat4) (u v : R4) : ℝ :=
  omega4 (M.mulVec u) v + omega4 u (M.mulVec v)

/-- Invariance under $I_4$: $\mathcal{L}_{I_4} \Omega_4 = 0$. -/
theorem lieDeriv_I4_omega4 (u v : R4) : lieDerivOmega4 I4_mat u v = 0 := by
  dsimp [lieDerivOmega4, omega4]
  simp
  ring

/-- Invariance under $J_4$: $\mathcal{L}_{J_4} \Omega_4 = 0$. -/
theorem lieDeriv_J4_omega4 (u v : R4) : lieDerivOmega4 J4_para u v = 0 := by
  dsimp [lieDerivOmega4, omega4]
  simp
  ring

/-- Invariance under $K_4$: $\mathcal{L}_{K_4} \Omega_4 = 0$. -/
theorem lieDeriv_K4_omega4 (u v : R4) : lieDerivOmega4 K4_para u v = 0 := by
  dsimp [lieDerivOmega4, omega4]
  simp
  ring

/-- Pure homothety dilatation in 4D: $\mathcal{L}_{c \cdot \mathbf{1}} \Omega_4 = 2c \Omega_4$. -/
theorem lieDeriv_homothety_omega4 (c : ℝ) (u v : R4) :
    lieDerivOmega4 (c • (1 : Mat4)) u v = 2 * c * omega4 u v := by
  dsimp [lieDerivOmega4, omega4]
  simp
  ring

/-! ## 5. The Associated 4D Metric Triplet -/

/-- The form associated with $I_4$: $\Omega_{I_4}(u, v) = \Omega_4(I_4 u, v)$. -/
def omegaI4 (u v : R4) : ℝ :=
  omega4 (I4_mat.mulVec u) v

/-- The form associated with $J_4$: $\Omega_{J_4}(u, v) = \Omega_4(J_4 u, v)$. -/
def omegaJ4 (u v : R4) : ℝ :=
  omega4 (J4_para.mulVec u) v

/-- The form associated with $K_4$: $\Omega_{K_4}(u, v) = \Omega_4(K_4 u, v)$. -/
def omegaK4 (u v : R4) : ℝ :=
  omega4 (K4_para.mulVec u) v

/-- Explicit expression: $\Omega_{I_4}(u, v) = u \cdot v$ (4D Euclidean metric). -/
theorem omegaI4_eq_euclidean (u v : R4) :
    omegaI4 u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 := by
  dsimp [omegaI4, omega4]
  simp
  ring

/-- Explicit expression: $\Omega_{J_4}(u, v) = -(u_0 v_0 + u_1 v_1 - u_2 v_2 - u_3 v_3)$ (neutral signature $(2, 2)$ metric). -/
theorem omegaJ4_eq_neutral (u v : R4) :
    omegaJ4 u v = -(u 0 * v 0 + u 1 * v 1 - u 2 * v 2 - u 3 * v 3) := by
  dsimp [omegaJ4, omega4]
  simp
  ring

/-- Explicit expression: $\Omega_{K_4}(u, v) = u_0 v_2 + u_1 v_3 + u_2 v_0 + u_3 v_1$ (hyperbolic split metric). -/
theorem omegaK4_eq_split (u v : R4) :
    omegaK4 u v = u 0 * v 2 + u 1 * v 3 + u 2 * v 0 + u 3 * v 1 := by
  dsimp [omegaK4, omega4]
  simp

/-! ## 6. Certified Structural Synthesis Package -/

/-- Certified structural synthesis package for 4D $\mathrm{Sp}(4, \mathbb{R})$ Para-Hyperkähler geometry. -/
structure Sp4ParaHyperkahlerSynthesis where
  i4_sq_neg_one : I4_mat * I4_mat = -1
  j4_sq_one : J4_para * J4_para = 1
  k4_sq_one : K4_para * K4_para = 1
  i4_in_sp4 : IsInSp4LieAlgebra I4_mat
  j4_in_sp4 : IsInSp4LieAlgebra J4_para
  k4_in_sp4 : IsInSp4LieAlgebra K4_para
  lie_deriv_i4_zero : ∀ (u v : R4), lieDerivOmega4 I4_mat u v = 0
  lie_deriv_j4_zero : ∀ (u v : R4), lieDerivOmega4 J4_para u v = 0
  lie_deriv_k4_zero : ∀ (u v : R4), lieDerivOmega4 K4_para u v = 0
  lie_deriv_homothety_scale : ∀ (c : ℝ) (u v : R4), lieDerivOmega4 (c • (1 : Mat4)) u v = 2 * c * omega4 u v
  omega_i4_is_euclidean : ∀ (u v : R4), omegaI4 u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3
  omega_j4_is_neutral : ∀ (u v : R4), omegaJ4 u v = -(u 0 * v 0 + u 1 * v 1 - u 2 * v 2 - u 3 * v 3)
  omega_k4_is_split : ∀ (u v : R4), omegaK4 u v = u 0 * v 2 + u 1 * v 3 + u 2 * v 0 + u 3 * v 1

/-- The verified canonical synthesis instance. -/
def sp4_parahyperkahler_synthesis : Sp4ParaHyperkahlerSynthesis where
  i4_sq_neg_one := I4_sq
  j4_sq_one := J4_sq
  k4_sq_one := K4_sq
  i4_in_sp4 := I4_in_sp4
  j4_in_sp4 := J4_in_sp4
  k4_in_sp4 := K4_in_sp4
  lie_deriv_i4_zero := lieDeriv_I4_omega4
  lie_deriv_j4_zero := lieDeriv_J4_omega4
  lie_deriv_k4_zero := lieDeriv_K4_omega4
  lie_deriv_homothety_scale := lieDeriv_homothety_omega4
  omega_i4_is_euclidean := omegaI4_eq_euclidean
  omega_j4_is_neutral := omegaJ4_eq_neutral
  omega_k4_is_split := omegaK4_eq_split

end InfoGeometry.Canonical.Sp4ParaHyperkahlerPresymplecticBridge
