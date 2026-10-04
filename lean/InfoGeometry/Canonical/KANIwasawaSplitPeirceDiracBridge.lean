import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Finite `2 × 2` matrix identities related to KAN coordinates

This file proves concrete determinant, trace, projector, and matrix-product
identities. It does not prove a global Iwasawa factorization, a parabolic
subgroup theorem, a Klein bottle group action, a bundle holonomy, or a
Dirac–Kähler differential-operator decomposition.

The matrix `matR = [[0,1],[1,0]]` is an element of `O(2)` and normalizes the
positive diagonal torus by swapping its diagonal entries. It is not in
`SO(2)` and does not centralize a nontrivial diagonal boost. Thus it represents
a Weyl-normalizer action in this matrix model, not an element of
`M = Z_K(A)` for the usual `SL(2,ℝ)` KAN decomposition.

The trace and determinant lemmas below concern the displayed matrices only;
they do not identify every trace contribution in a general Lie algebra or
geometric Dirac operator.
-/

noncomputable section

namespace InfoGeometry.Canonical.KANIwasawaSplitPeirceDirac

open Matrix

set_option linter.unusedVariables false

/-! ### Stratum 1: Concrete $2 \times 2$ matrices used as $K$, $A$, and $N$ coordinates -/

/-- Compact elliptic rotation matrix in $\mathrm{SO}(2)$. -/
def matK_rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The coordinate-swap reflection in `O(2)`, a Weyl-normalizer matrix for the
positive diagonal subgroup. It is not in `SO(2)` and is not in the centralizer
`Z_K(A)` for the usual `SL(2,ℝ)` KAN decomposition. -/
def matR : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- Diagonal matrix with entries `a₁` and `a₂`.  It is invertible only when
both entries are nonzero; within `SL(2, ℝ)`, the diagonal subgroup additionally
satisfies `a₁ * a₂ = 1`. -/
def matA (a₁ a₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a₁, 0; 0, a₂]

/-- One-parameter split torus in `SL(2, ℝ)`, with opposite coordinate
weights.  Its determinant is one, so this boost is a relative dilation rather
than a volume homothety. -/
def matA_boost (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  matA (Real.exp t) (Real.exp (-t))

/-- Nilpotent parabolic horocycle matrix $N(x) = \mathbf{1} + x e_+$. -/
def matN (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, x; 0, 1]

/-- The composite Iwasawa product $k \cdot a \cdot n$. -/
def kanProduct (k a n : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  k * a * n

/-- Rotation has unit determinant: $\det(K_\theta) = 1$. -/
theorem matK_rot_det (θ : ℝ) : (matK_rot θ).det = 1 := by
  simp [matK_rot, Matrix.det_fin_two]
  have h := Real.cos_sq_add_sin_sq θ
  linarith

/-- Reflection has determinant $-1$: $\det(R) = -1$. -/
theorem matR_det : matR.det = -1 := by
  simp [matR, Matrix.det_fin_two]

/-- Reflection is an involution: $R^2 = \mathbf{1}$. -/
theorem matR_sq : matR * matR = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matR]

/-- Determinant of the split abelian torus: $\det(A) = a_1 a_2$. -/
theorem matA_det (a₁ a₂ : ℝ) : (matA a₁ a₂).det = a₁ * a₂ := by
  simp [matA, Matrix.det_fin_two]

/-- One-parameter hyperbolic boost has determinant 1. -/
theorem matA_boost_det (t : ℝ) : (matA_boost t).det = 1 := by
  dsimp [matA_boost]
  rw [matA_det, ← Real.exp_add]
  have h : t + -t = 0 := by ring
  rw [h, Real.exp_zero]

/-- Torus multiplication law: $A(a_1, a_2) A(b_1, b_2) = A(a_1 b_1, a_2 b_2)$. -/
theorem matA_mul (a₁ a₂ b₁ b₂ : ℝ) :
    matA a₁ a₂ * matA b₁ b₂ = matA (a₁ * b₁) (a₂ * b₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA]

/-- Nilpotent horocycle shear has determinant 1: $\det(N) = 1$. -/
theorem matN_det (x : ℝ) : (matN x).det = 1 := by
  simp [matN, Matrix.det_fin_two]

/-- Horocycle shear addition law: $N(x) N(y) = N(x + y)$. -/
theorem matN_mul (x y : ℝ) :
    matN x * matN y = matN (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matN, add_comm]

/-- General Iwasawa determinant multiplicativity. -/
theorem kanProduct_det (k a n : Matrix (Fin 2) (Fin 2) ℝ) :
    (kanProduct k a n).det = k.det * a.det * n.det := by
  dsimp [kanProduct]
  rw [Matrix.det_mul, Matrix.det_mul]

/-- Determinant multiplicativity when the right factor is the displayed
unipotent matrix `N(x)`.  This is a matrix identity, not a scale/parity/phase
decomposition of a frame group. -/
theorem kanProduct_det_of_unipotent (k a : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) :
    (kanProduct k a (matN x)).det = k.det * a.det := by
  rw [kanProduct_det, matN_det, mul_one]

/-! ### Stratum 2: Lie Algebra Trace Support on $\mathfrak{a}$ -/

/-- Skew-symmetric core Lie algebra generator: $\mathfrak{k} = \mathfrak{so}(2)$. -/
def mat_k_gen (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -ω; ω, 0]

/-- Abelian Cartan Lie algebra generator: $\mathfrak{a}$. -/
def mat_a_gen (t₁ t₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![t₁, 0; 0, t₂]

/-- Nilpotent horocycle Lie algebra generator: $\mathfrak{n}$. -/
def mat_n_gen (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, x; 0, 0]

/-- $\mathfrak{k}$ is traceless: $\operatorname{tr}(X_\mathfrak{k}) = 0$. -/
theorem mat_k_gen_trace (ω : ℝ) : (mat_k_gen ω).trace = 0 := by
  simp [mat_k_gen, Matrix.trace, Fin.sum_univ_two]

/-- $\mathfrak{n}$ is strictly nilpotent: $X_\mathfrak{n}^2 = 0$. -/
theorem mat_n_gen_sq (x : ℝ) : mat_n_gen x * mat_n_gen x = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat_n_gen]

/-- $\mathfrak{n}$ is traceless: $\operatorname{tr}(X_\mathfrak{n}) = 0$. -/
theorem mat_n_gen_trace (x : ℝ) : (mat_n_gen x).trace = 0 := by
  simp [mat_n_gen, Matrix.trace, Fin.sum_univ_two]

/-- The trace of $\mathfrak{a}$ is the sum of the scale weights: $\operatorname{tr}(X_\mathfrak{a}) = t_1 + t_2$. -/
theorem mat_a_gen_trace (t₁ t₂ : ℝ) : (mat_a_gen t₁ t₂).trace = t₁ + t₂ := by
  simp [mat_a_gen, Matrix.trace, Fin.sum_univ_two]

/-- The diagonal generator in the determinant-one split Cartan direction is
traceless. -/
theorem mat_a_gen_trace_opposite (t : ℝ) :
    (mat_a_gen t (-t)).trace = 0 := by
  rw [mat_a_gen_trace]
  ring

/-- 
For the displayed $2 \times 2$ matrices, the trace of the sum equals the
trace of the diagonal matrix. This is a finite matrix identity; this file does
not define a Lie algebra decomposition or a global KAN factorization.
-/
theorem kan_trace_supported_on_a (ω t₁ t₂ x : ℝ) :
    (mat_k_gen ω + mat_a_gen t₁ t₂ + mat_n_gen x).trace = (mat_a_gen t₁ t₂).trace := by
  rw [Matrix.trace_add, Matrix.trace_add, mat_k_gen_trace, mat_n_gen_trace]
  ring

/-! ### Stratum 3: $C\ell(1, 1)$, Split Peirce Projectors, and Horocyclic $N$-Transitions -/

/-- Positive split Peirce projector: $P_+ = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def P_plus : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 0]

/-- Negative split Peirce projector: $P_- = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def P_minus : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 0, 1]

/-- Nilpotent lightcone step operator: $e_+ = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
def e_plus : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 0, 0]

theorem P_plus_sq : P_plus * P_plus = P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus]

theorem P_minus_sq : P_minus * P_minus = P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_minus]

theorem P_plus_mul_minus : P_plus * P_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus]

theorem P_minus_mul_plus : P_minus * P_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus]

theorem P_plus_add_minus : P_plus + P_minus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus]

theorem e_plus_sq : e_plus * e_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e_plus]

/-- The split Peirce projectors are spectral eigenprojectors of the $A$-action on the left. -/
theorem A_eigen_P_plus (a₁ a₂ : ℝ) :
    matA a₁ a₂ * P_plus = a₁ • P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, P_plus]

theorem A_eigen_P_minus (a₁ a₂ : ℝ) :
    matA a₁ a₂ * P_minus = a₂ • P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, P_minus]

/-- Unipotent shear expansion: $N(x) = \mathbf{1} + x e_+$. -/
theorem matN_eq_one_add_smul (x : ℝ) :
    matN x = 1 + x • e_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matN, e_plus]

/-- $N$ leaves the positive Peirce subspace stable: $P_+ N(x) P_+ = P_+$. -/
theorem P_plus_matN_P_plus (x : ℝ) :
    P_plus * matN x * P_plus = P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, matN]

/-- $N$ leaves the negative Peirce subspace stable: $P_- N(x) P_- = P_-$. -/
theorem P_minus_matN_P_minus (x : ℝ) :
    P_minus * matN x * P_minus = P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_minus, matN]

/-- $N$ has no backward transition: $P_- N(x) P_+ = 0$. -/
theorem P_minus_matN_P_plus (x : ℝ) :
    P_minus * matN x * P_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_minus, matN, P_plus]

/--
$N$-Mediated Peirce Transition Theorem:
The unipotent horocycle subgroup $N(x)$ acts as a one-way lightcone shear that
maps the negative Peirce polarization $P_-$ directly into the positive channel $P_+$:
$P_+ N(x) P_- = x e_+$.
-/
theorem P_plus_matN_P_minus (x : ℝ) :
    P_plus * matN x * P_minus = x • e_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, matN, P_minus, e_plus]

/-! ### Weyl-normalizer action on the boost and projectors -/

/--
The coordinate-swap matrix conjugates the displayed boost to its inverse:
$R \cdot A(t) \cdot R = A(-t)$.
-/
theorem matR_conjugates_boost (t : ℝ) :
    matR * matA_boost t * matR = matA_boost (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matR, matA_boost, matA]

/--
Conjugation by the coordinate-swap matrix exchanges the two diagonal
projectors:
$R \cdot P_+ \cdot R = P_-$.
-/
theorem matR_swaps_peirce_plus :
    matR * P_plus * matR = P_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matR, P_plus, P_minus]

/-- $R \cdot P_- \cdot R = P_+$. -/
theorem matR_swaps_peirce_minus :
    matR * P_minus * matR = P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matR, P_minus, P_plus]

/-- Double traversal restores positive projector: $R^2 P_+ R^2 = P_+$. -/
theorem matR_restores_peirce_plus :
    matR * (matR * P_plus * matR) * matR = P_plus := by
  rw [matR_swaps_peirce_plus, matR_swaps_peirce_minus]

/-- Double traversal restores negative projector: $R^2 P_- R^2 = P_-$. -/
theorem matR_restores_peirce_minus :
    matR * (matR * P_minus * matR) * matR = P_minus := by
  rw [matR_swaps_peirce_minus, matR_swaps_peirce_plus]

/-! ### Off-diagonal decomposition for an explicit matrix -/

/--
An off-diagonal `2 × 2` matrix satisfies `P_± D P_± = 0` for the displayed
coordinate projectors. No differential operator is defined here.
-/
def matDirac (d₁ d₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, d₁; d₂, 0]

theorem matDirac_peirce_plus_zero (d₁ d₂ : ℝ) :
    P_plus * matDirac d₁ d₂ * P_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, matDirac]

theorem matDirac_peirce_minus_zero (d₁ d₂ : ℝ) :
    P_minus * matDirac d₁ d₂ * P_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_minus, matDirac]

theorem matDirac_off_diagonal (d₁ d₂ : ℝ) :
    matDirac d₁ d₂ = P_plus * matDirac d₁ d₂ * P_minus + P_minus * matDirac d₁ d₂ * P_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P_plus, P_minus, matDirac]

end InfoGeometry.Canonical.KANIwasawaSplitPeirceDirac
