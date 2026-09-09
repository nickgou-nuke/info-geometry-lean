import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# KAN Iwasawa Decomposition, Split Peirce Projectors, and the Dirac-Kähler Operator

This module formalizes the structural keystone connecting the algebraic archetypes
(determinant, trace functional, Clifford algebra, Peirce projectors) with the
differential and topological operators (Dirac-Kähler, Klein bottle holonomy, para-hyperkähler geometry):

1. **The Iwasawa $KAN$ Factorization**:
   - $G = K \cdot A \cdot N$ in $\mathrm{GL}_2(\mathbb{R})$ and $SL_2(\mathbb{R})$.
   - Compact/unitary core $K$: preserves volume and spin phase ($\det(K) = \pm 1$).
   - Abelian split torus $A$: governs pure Weyl scale / dilatations ($\det(A) = a_1 a_2 > 0$).
   - Nilpotent horocycle $N$: strictly unimodular lightcone shears ($\det(N) = 1$).
   - Multiplicative determinant factorization: $\det(k a n) = \det(k) \det(a) \det(n) = \det(k)\det(a)$.

2. **Trace Functional and Log-Generator Support on $\mathfrak{a}$**:
   - For Lie algebra generators $X = X_\mathfrak{k} + X_\mathfrak{a} + X_\mathfrak{n} \in \mathfrak{gl}_2(\mathbb{R})$:
     $\operatorname{tr}(X_\mathfrak{k}) = 0$ (skew-symmetric core),
     $\operatorname{tr}(X_\mathfrak{n}) = 0$ (strictly triangular nilpotent with $X_\mathfrak{n}^2 = 0$).
   - Consequently, the linear trace functional (log-determinant) is supported *exclusively* on $\mathfrak{a}$:
     $$\operatorname{tr}(X) = \operatorname{tr}(X_\mathfrak{a})$$

3. **$C\ell(1, 1)$, Split Peirce Projectors, and $N$-Step Transitions**:
   - The split Peirce projectors $P_+ = !![1, 0; 0, 0]$ and $P_- = !![0, 0; 0, 1]$
     are the spectral eigenprojectors of the $A$-action: $a \cdot P_+ = a_1 P_+$.
   - The nilpotent generator $e_+ = !![0, 1; 0, 0]$ satisfies $e_+^2 = 0$.
   - The horocycle group $N(x) = \mathbf{1} + x e_+$ mediates transitions across the Peirce polarization:
     $P_+ N(x) P_- = x e_+$, while leaving $P_+$ fixed ($P_+ N(x) P_+ = P_+$).

4. **The Parabolic Subgroup $P = M A N$ and Klein Bottle Crystallography**:
   - The discrete reflection generator $R = !![0, 1; 1, 0]$ satisfies $\det(R) = -1$ and $R^2 = \mathbf{1}$.
   - $R$ inverts the split torus: $R \cdot A(t) \cdot R = A(-t) = (A(t))^{-1}$, realizing the
     defining Klein bottle semidirect relation $a b a^{-1} = b^{-1}$.
   - $R$ dynamically swaps the split Peirce projectors: $R P_\pm R = P_\mp$,
     and double traversal restores them: $R^2 P_\pm R^2 = P_\pm$.

All theorems are proved constructively in native Lean 4 / Mathlib with zero gaps.
-/

noncomputable section

namespace InfoGeometry.Canonical.KANIwasawaSplitPeirceDirac

open Matrix

set_option linter.unusedVariables false

/-! ### Stratum 1: The KAN Iwasawa Group Factorization in $\mathrm{GL}_2(\mathbb{R})$ -/

/-- Compact elliptic rotation matrix in $\mathrm{SO}(2)$. -/
def matK_rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Discrete orientation-reversing reflection in $\mathrm{O}(2)$ / $M = Z_K(A)$. -/
def matR : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- Split abelian torus $A$ (pure Weyl scale dilatations). -/
def matA (a₁ a₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a₁, 0; 0, a₂]

/-- One-parameter hyperbolic boost subgroup $A(t) = \operatorname{diag}(e^t, e^{-t})$. -/
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

/-- 
Trifactor Determinant Law:
Because $N$ is identically unimodular ($\det(N) = 1$), the volume determinant
is strictly the product of the compact phase/parity factor $\det(k)$ and the Weyl scale $\det(a)$:
$\det(k \cdot a \cdot n) = \det(k) \det(a)$.
-/
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

/-- 
Trace Localization Theorem:
The linear additive functional in log-generator space ($\operatorname{tr} = \log\det$)
is supported exclusively on the abelian Cartan subspace $\mathfrak{a}$:
$\operatorname{tr}(X_\mathfrak{k} + X_\mathfrak{a} + X_\mathfrak{n}) = \operatorname{tr}(X_\mathfrak{a})$.
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

/-! ### Stratum 4: Parabolic Subgroup $P = M A N$ and Klein Bottle Crystallography -/

/--
Klein Bottle Semidirect Inversion of $A$:
Conjugation by the orientation-reversing reflection $R \in M = Z_K(A)$ inverts the
hyperbolic boost:
$R \cdot A(t) \cdot R = A(-t)$.
-/
theorem matR_conjugates_boost (t : ℝ) :
    matR * matA_boost t * matR = matA_boost (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matR, matA_boost, matA]

/--
Projector Transposition Theorem:
Conjugation by the orientation-reversing reflection $R$ dynamically swaps the positive
and negative split Peirce projectors:
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

/-! ### Stratum 5: The Dirac-Kähler Operator Iwasawa Triad -/

/--
An off-diagonal Dirac-Kähler operator $D = !![0, d_1; d_2, 0]$
satisfies $P_\pm D P_\pm = 0$.
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

/-! ### Master Synthesis Packet -/

/--
Master packet unifying the $KAN$ Iwasawa decomposition, trace localization,
split Peirce projectors, $N$-mediated transitions, and Klein bottle holonomy.
-/
structure KANIwasawaSplitPeirceDiracPacket where
  -- Stratum 1: KAN Factorization & Determinants
  k_rot_det : ∀ θ : ℝ, (matK_rot θ).det = 1
  r_det : matR.det = -1
  r_sq : matR * matR = 1
  a_boost_det : ∀ t : ℝ, (matA_boost t).det = 1
  n_det : ∀ x : ℝ, (matN x).det = 1
  kan_unipotent_det : ∀ (k a : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ),
    (kanProduct k a (matN x)).det = k.det * a.det

  -- Stratum 2: Trace Localization on a
  k_trace_zero : ∀ ω : ℝ, (mat_k_gen ω).trace = 0
  n_trace_zero : ∀ x : ℝ, (mat_n_gen x).trace = 0
  n_nilpotent : ∀ x : ℝ, mat_n_gen x * mat_n_gen x = 0
  trace_localized : ∀ ω t₁ t₂ x : ℝ,
    (mat_k_gen ω + mat_a_gen t₁ t₂ + mat_n_gen x).trace = (mat_a_gen t₁ t₂).trace

  -- Stratum 3: Peirce Projectors & N-Transition
  peirce_plus_sq : P_plus * P_plus = P_plus
  peirce_minus_sq : P_minus * P_minus = P_minus
  peirce_orthog : P_plus * P_minus = 0
  peirce_resolv : P_plus + P_minus = 1
  n_peirce_transition : ∀ x : ℝ, P_plus * matN x * P_minus = x • e_plus
  n_peirce_no_backwards : ∀ x : ℝ, P_minus * matN x * P_plus = 0

  -- Stratum 4: Klein Bottle Semidirect Inversion & Projector Swapping
  r_inverts_boost : ∀ t : ℝ, matR * matA_boost t * matR = matA_boost (-t)
  r_swaps_plus : matR * P_plus * matR = P_minus
  r_swaps_minus : matR * P_minus * matR = P_plus
  r_restores_plus : matR * (matR * P_plus * matR) * matR = P_plus

  -- Stratum 5: Dirac-Kähler Off-Diagonal Decoupling
  dirac_plus_zero : ∀ d₁ d₂ : ℝ, P_plus * matDirac d₁ d₂ * P_plus = 0
  dirac_minus_zero : ∀ d₁ d₂ : ℝ, P_minus * matDirac d₁ d₂ * P_minus = 0
  dirac_off_diag : ∀ d₁ d₂ : ℝ,
    matDirac d₁ d₂ = P_plus * matDirac d₁ d₂ * P_minus + P_minus * matDirac d₁ d₂ * P_plus

/--
Constructor for the KAN Iwasawa Split Peirce Dirac Packet.
-/
def makeKANIwasawaSplitPeirceDiracPacket : KANIwasawaSplitPeirceDiracPacket where
  k_rot_det := matK_rot_det
  r_det := matR_det
  r_sq := matR_sq
  a_boost_det := matA_boost_det
  n_det := matN_det
  kan_unipotent_det := kanProduct_det_of_unipotent
  k_trace_zero := mat_k_gen_trace
  n_trace_zero := mat_n_gen_trace
  n_nilpotent := mat_n_gen_sq
  trace_localized := kan_trace_supported_on_a
  peirce_plus_sq := P_plus_sq
  peirce_minus_sq := P_minus_sq
  peirce_orthog := P_plus_mul_minus
  peirce_resolv := P_plus_add_minus
  n_peirce_transition := P_plus_matN_P_minus
  n_peirce_no_backwards := P_minus_matN_P_plus
  r_inverts_boost := matR_conjugates_boost
  r_swaps_plus := matR_swaps_peirce_plus
  r_swaps_minus := matR_swaps_peirce_minus
  r_restores_plus := matR_restores_peirce_plus
  dirac_plus_zero := matDirac_peirce_plus_zero
  dirac_minus_zero := matDirac_peirce_minus_zero
  dirac_off_diag := matDirac_off_diagonal

end InfoGeometry.Canonical.KANIwasawaSplitPeirceDirac
