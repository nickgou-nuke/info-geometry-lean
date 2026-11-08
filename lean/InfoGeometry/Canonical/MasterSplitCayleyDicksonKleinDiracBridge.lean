import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.KleinPresentedGroup

/-!
# Finite split algebra and Klein-relation calculations

This file contains explicit split-complex coordinate operations, split-quaternion
matrix identities, a generic Peirce off-diagonal lemma, and affine maps satisfying
the Klein-bottle group relator. Its sign representations are algebraic homomorphisms
from the presented Klein group to `Units ℤ`, not Pin structures. The matrix results
do not define a differential operator or a manifold. In particular, the affine
glide's determinant alone does not imply that it swaps an independently chosen
para-complex involution.
-/

noncomputable section

namespace InfoGeometry.Canonical.MasterSplitCayleyDicksonKleinDirac

/-! ### Stratum 1: Split Cayley-Dickson Doubling (Step 1: $\mathbb{R} \to \mathbb{D}$) -/

/--
Split-complex numbers $\mathbb{D} = R[\tau] / (\tau^2 - 1)$ obtained by
split Cayley-Dickson doubling with parameter $\gamma = +1$.
-/
structure SplitComplex (R : Type*) where
  re : R
  hyp : R
  deriving DecidableEq

namespace SplitComplex

@[ext]
theorem ext {R : Type*} {x y : SplitComplex R} (hre : x.re = y.re) (hhyp : x.hyp = y.hyp) : x = y := by
  cases x; cases y; simp_all

variable {R : Type*} [CommRing R]

def add (x y : SplitComplex R) : SplitComplex R := ⟨x.re + y.re, x.hyp + y.hyp⟩
def sub (x y : SplitComplex R) : SplitComplex R := ⟨x.re - y.re, x.hyp - y.hyp⟩
def neg (x : SplitComplex R) : SplitComplex R := ⟨-x.re, -x.hyp⟩

/-- Split Cayley-Dickson product with parameter $\gamma = +1$. -/
def mul (x y : SplitComplex R) : SplitComplex R :=
  ⟨x.re * y.re + x.hyp * y.hyp, x.re * y.hyp + x.hyp * y.re⟩

def zero : SplitComplex R := ⟨0, 0⟩
def one : SplitComplex R := ⟨1, 0⟩
def tau : SplitComplex R := ⟨0, 1⟩
def conj (x : SplitComplex R) : SplitComplex R := ⟨x.re, -x.hyp⟩
def normSq (x : SplitComplex R) : R := x.re * x.re - x.hyp * x.hyp

/-- The hyperbolic involution: $\tau^2 = 1$. -/
theorem tau_sq : mul tau tau = (one : SplitComplex R) := by
  ext <;> dsimp [mul, tau, one] <;> ring

/-- Conjugation negates the hyperbolic generator: $\overline{\tau} = -\tau$. -/
theorem tau_conj : conj (tau : SplitComplex R) = neg tau := by
  ext <;> simp [conj, tau, neg]

/-- Conjugation is an algebra anti-automorphism (automorphism since commutative). -/
theorem conj_mul (x y : SplitComplex R) : conj (mul x y) = mul (conj x) (conj y) := by
  ext <;> dsimp [conj, mul] <;> ring

/-- The split norm is multiplicative: $N(x y) = N(x) N(y)$. -/
theorem normSq_mul (x y : SplitComplex R) : normSq (mul x y) = normSq x * normSq y := by
  dsimp [normSq, mul]
  ring

/-- Zero divisor on the lightcone: $(1 + \tau)(1 - \tau) = 0$. -/
theorem split_zero_divisor :
    mul (add one tau) (sub one tau) = (zero : SplitComplex R) := by
  ext <;> dsimp [mul, add, sub, one, tau, zero] <;> ring

/-- Split Peirce positive projector: $P_+ = \frac{1}{2}(1 + \tau)$. -/
def peirceP (half : R) : SplitComplex R := ⟨half, half⟩

/-- Split Peirce negative projector: $P_- = \frac{1}{2}(1 - \tau)$. -/
def peirceM (half : R) : SplitComplex R := ⟨half, -half⟩

/-- $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem peirceP_sq (half : R) (h_half : half + half = 1) :
    mul (peirceP half) (peirceP half) = peirceP half := by
  apply ext
  · dsimp [mul, peirceP]
    calc half * half + half * half = half * (half + half) := by ring
    _ = half * 1 := by rw [h_half]
    _ = half := by ring
  · dsimp [mul, peirceP]
    calc half * half + half * half = half * (half + half) := by ring
    _ = half * 1 := by rw [h_half]
    _ = half := by ring

/-- $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem peirceM_sq (half : R) (h_half : half + half = 1) :
    mul (peirceM half) (peirceM half) = peirceM half := by
  apply ext
  · dsimp [mul, peirceM]
    calc half * half + (-half) * (-half) = half * (half + half) := by ring
    _ = half * 1 := by rw [h_half]
    _ = half := by ring
  · dsimp [mul, peirceM]
    calc half * (-half) + (-half) * half = - (half * (half + half)) := by ring
    _ = - (half * 1) := by rw [h_half]
    _ = -half := by ring

/-- Orthogonality: $P_+ \cdot P_- = 0$. -/
theorem peirce_orthogonal (half : R) :
    mul (peirceP half) (peirceM half) = zero := by
  ext <;> dsimp [mul, peirceP, peirceM, zero] <;> ring

/-- Completeness / Partition of Unity: $P_+ + P_- = 1$. -/
theorem peirce_partition (half : R) (h_half : half + half = 1) :
    add (peirceP half) (peirceM half) = one := by
  apply ext
  · dsimp [add, peirceP, peirceM, one]
    exact h_half
  · dsimp [add, peirceP, peirceM, one]
    ring

end SplitComplex

/-! ### Stratum 2: Coquaternions / Split Quaternions ($\mathbb{H}' \cong \mathrm{Mat}_2(R)$) -/

/-- Identity matrix in $\mathrm{Mat}_2(R)$. -/
def matOne {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, 1]

/-- Elliptic generator $I$ with $I^2 = -\mathbf{1}$. -/
def matI {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, -1; 1, 0]

/-- Hyperbolic generator $J$ with $J^2 = +\mathbf{1}$. -/
def matJ {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- Hyperbolic generator $K$ with $K^2 = +\mathbf{1}$. -/
def matK {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, 0]

theorem coquat_i_sq {R : Type*} [CommRing R] :
    matI (R := R) * matI = - matOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matI, matOne]

theorem coquat_j_sq {R : Type*} [CommRing R] :
    matJ (R := R) * matJ = matOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matJ, matOne]

theorem coquat_k_sq {R : Type*} [CommRing R] :
    matK (R := R) * matK = matOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matK, matOne]

theorem coquat_ij {R : Type*} [CommRing R] :
    matI (R := R) * matJ = matK := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matI, matJ, matK]

theorem coquat_ji {R : Type*} [CommRing R] :
    matJ (R := R) * matI = - matK := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matI, matJ, matK]

theorem coquat_jk {R : Type*} [CommRing R] :
    matJ (R := R) * matK = - matI := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matI, matJ, matK]

theorem coquat_kj {R : Type*} [CommRing R] :
    matK (R := R) * matJ = matI := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matI, matJ, matK]

theorem coquat_ki {R : Type*} [CommRing R] :
    matK (R := R) * matI = matJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matI, matJ, matK]

theorem coquat_ik {R : Type*} [CommRing R] :
    matI (R := R) * matK = - matJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matI, matJ, matK]

/-- Concrete matrix Peirce projector $P_+ = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$. -/
def matPeircePlusJ {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, 0]

/-- Concrete matrix Peirce projector $P_- = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$. -/
def matPeirceMinusJ {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 0; 0, 1]

theorem matPeircePlusJ_sq {R : Type*} [CommRing R] :
    matPeircePlusJ (R := R) * matPeircePlusJ = matPeircePlusJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matPeircePlusJ]

theorem matPeirceMinusJ_sq {R : Type*} [CommRing R] :
    matPeirceMinusJ (R := R) * matPeirceMinusJ = matPeirceMinusJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matPeirceMinusJ]

theorem matPeirce_orthog {R : Type*} [CommRing R] :
    matPeircePlusJ (R := R) * matPeirceMinusJ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matPeircePlusJ, matPeirceMinusJ]

theorem matPeirce_complete {R : Type*} [CommRing R] :
    matPeircePlusJ (R := R) + matPeirceMinusJ = matOne := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matPeircePlusJ, matPeirceMinusJ, matOne]

/-- A general off-diagonal operator matrix in $\mathrm{Mat}_2(R)$. -/
def matDiracOffDiag {R : Type*} [CommRing R] (d01 d10 : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, d01; d10, 0]

theorem matDiracOffDiag_anticomm {R : Type*} [CommRing R] (d01 d10 : R) :
    matDiracOffDiag d01 d10 * matJ + matJ * matDiracOffDiag d01 d10 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matDiracOffDiag, matJ]

theorem matDirac_peirce_plus_plus_zero {R : Type*} [CommRing R] (d01 d10 : R) :
    matPeircePlusJ (R := R) * matDiracOffDiag d01 d10 * matPeircePlusJ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matPeircePlusJ, matDiracOffDiag]

theorem matDirac_peirce_minus_minus_zero {R : Type*} [CommRing R] (d01 d10 : R) :
    matPeirceMinusJ (R := R) * matDiracOffDiag d01 d10 * matPeirceMinusJ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matPeirceMinusJ, matDiracOffDiag]

theorem matDirac_off_diag_decomposition {R : Type*} [CommRing R] (d01 d10 : R) :
    matDiracOffDiag d01 d10 =
      matPeircePlusJ * matDiracOffDiag d01 d10 * matPeirceMinusJ +
      matPeirceMinusJ * matDiracOffDiag d01 d10 * matPeircePlusJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matPeircePlusJ, matPeirceMinusJ, matDiracOffDiag]

/-! ### Stratum 3: Abstract Dirac-Kähler Off-Diagonal Decoupling -/

/-- Positive Peirce projector: $P_+ = \frac{1}{2}(1 + J)$. -/
def peircePlus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) : A :=
  (1/2 : ℝ) • (1 + J)

/-- Negative Peirce projector: $P_- = \frac{1}{2}(1 - J)$. -/
def peirceMinus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) : A :=
  (1/2 : ℝ) • (1 - J)

/-- $P_+$ is idempotent: $P_+^2 = P_+$. -/
theorem peircePlus_sq {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peircePlus J * peircePlus J = peircePlus J := by
  simp [peircePlus, smul_smul, hJ, smul_add, add_mul, mul_add]
  module

/-- $P_-$ is idempotent: $P_-^2 = P_-$. -/
theorem peirceMinus_sq {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peirceMinus J * peirceMinus J = peirceMinus J := by
  simp [peirceMinus, smul_smul, hJ, smul_sub, sub_mul, mul_sub]
  module

/-- Orthogonality: $P_+ \cdot P_- = 0$. -/
theorem peircePlus_mul_minus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peircePlus J * peirceMinus J = 0 := by
  simp [peircePlus, peirceMinus, smul_smul, hJ, smul_sub, smul_add, add_mul, mul_sub]
  module

/-- Orthogonality: $P_- \cdot P_+ = 0$. -/
theorem peirceMinus_mul_plus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) (hJ : J * J = 1) :
    peirceMinus J * peircePlus J = 0 := by
  simp [peircePlus, peirceMinus, smul_smul, hJ, smul_sub, smul_add, mul_add, sub_mul]

/-- Completeness / Resolution of Identity: $P_+ + P_- = 1$. -/
theorem peircePlus_add_minus {A : Type*} [Ring A] [Algebra ℝ A] (J : A) :
    peircePlus J + peirceMinus J = 1 := by
  simp [peircePlus, peirceMinus, smul_add, smul_sub]
  module

/-- Chiral intertwining: $P_+ D = D P_-$. -/
theorem peircePlus_mul_dirac {A : Type*} [Ring A] [Algebra ℝ A]
    (J D : A) (h_chiral : D * J + J * D = 0) :
    peircePlus J * D = D * peirceMinus J := by
  dsimp [peircePlus, peirceMinus]
  have h_anti : J * D = - (D * J) := by
    calc J * D = (D * J + J * D) - D * J := by abel
    _ = 0 - D * J := by rw [h_chiral]
    _ = - (D * J) := by simp
  calc
    peircePlus J * D = ((1/2 : ℝ) • (1 + J)) * D := rfl
    _ = (1/2 : ℝ) • ((1 + J) * D) := by rw [smul_mul_assoc]
    _ = (1/2 : ℝ) • (D + J * D) := by rw [add_mul, one_mul]
    _ = (1/2 : ℝ) • (D - D * J) := by rw [h_anti, sub_eq_add_neg]
    _ = (1/2 : ℝ) • (D * (1 - J)) := by rw [mul_sub, mul_one]
    _ = D * ((1/2 : ℝ) • (1 - J)) := by rw [mul_smul_comm]
    _ = D * peirceMinus J := rfl

/-- Chiral intertwining: $P_- D = D P_+$. -/
theorem peirceMinus_mul_dirac {A : Type*} [Ring A] [Algebra ℝ A]
    (J D : A) (h_chiral : D * J + J * D = 0) :
    peirceMinus J * D = D * peircePlus J := by
  dsimp [peircePlus, peirceMinus]
  have h_anti : J * D = - (D * J) := by
    calc J * D = (D * J + J * D) - D * J := by abel
    _ = 0 - D * J := by rw [h_chiral]
    _ = - (D * J) := by simp
  calc
    peirceMinus J * D = ((1/2 : ℝ) • (1 - J)) * D := rfl
    _ = (1/2 : ℝ) • ((1 - J) * D) := by rw [smul_mul_assoc]
    _ = (1/2 : ℝ) • (D - J * D) := by rw [sub_mul, one_mul]
    _ = (1/2 : ℝ) • (D + D * J) := by rw [h_anti, sub_neg_eq_add]
    _ = (1/2 : ℝ) • (D * (1 + J)) := by rw [mul_add, mul_one]
    _ = D * ((1/2 : ℝ) • (1 + J)) := by rw [mul_smul_comm]
    _ = D * peircePlus J := rfl

/-- Off-diagonal annihilation: $P_+ D P_+ = 0$. -/
theorem peircePlus_dirac_peircePlus_zero {A : Type*} [Ring A] [Algebra ℝ A]
    (J D : A) (hJ : J * J = 1) (h_chiral : D * J + J * D = 0) :
    peircePlus J * D * peircePlus J = 0 := by
  calc
    peircePlus J * D * peircePlus J = (peircePlus J * D) * peircePlus J := by rw [mul_assoc]
    _ = (D * peirceMinus J) * peircePlus J := by rw [peircePlus_mul_dirac J D h_chiral]
    _ = D * (peirceMinus J * peircePlus J) := by rw [mul_assoc]
    _ = D * 0 := by rw [peirceMinus_mul_plus J hJ]
    _ = 0 := by rw [mul_zero]

/-- Off-diagonal annihilation: $P_- D P_- = 0$. -/
theorem peirceMinus_dirac_peirceMinus_zero {A : Type*} [Ring A] [Algebra ℝ A]
    (J D : A) (hJ : J * J = 1) (h_chiral : D * J + J * D = 0) :
    peirceMinus J * D * peirceMinus J = 0 := by
  calc
    peirceMinus J * D * peirceMinus J = (peirceMinus J * D) * peirceMinus J := by rw [mul_assoc]
    _ = (D * peircePlus J) * peirceMinus J := by rw [peirceMinus_mul_dirac J D h_chiral]
    _ = D * (peircePlus J * peirceMinus J) := by rw [mul_assoc]
    _ = D * 0 := by rw [peircePlus_mul_minus J hJ]
    _ = 0 := by rw [mul_zero]

/-- 
Off-Diagonal Dirac-Kähler Decomposition Theorem:
$D = P_+ D P_- + P_- D P_+ = \begin{pmatrix} 0 & D^- \\ D^+ & 0 \end{pmatrix}$.
-/
theorem dirac_off_diagonal_split {A : Type*} [Ring A] [Algebra ℝ A]
    (J D : A) (hJ : J * J = 1) (h_chiral : D * J + J * D = 0) :
    D = peircePlus J * D * peirceMinus J + peirceMinus J * D * peircePlus J := by
  have h_one : peircePlus J + peirceMinus J = 1 := peircePlus_add_minus J
  have h_plus_plus := peircePlus_dirac_peircePlus_zero J D hJ h_chiral
  have h_minus_minus := peirceMinus_dirac_peirceMinus_zero J D hJ h_chiral
  calc
    D = 1 * D * 1 := by rw [one_mul, mul_one]
    _ = (peircePlus J + peirceMinus J) * D * (peircePlus J + peirceMinus J) := by rw [h_one]
    _ = (peircePlus J * D + peirceMinus J * D) * (peircePlus J + peirceMinus J) := by rw [add_mul]
    _ = peircePlus J * D * peircePlus J + peircePlus J * D * peirceMinus J +
        (peirceMinus J * D * peircePlus J + peirceMinus J * D * peirceMinus J) := by
      rw [add_mul, mul_add, mul_add]
    _ = 0 + peircePlus J * D * peirceMinus J +
        (peirceMinus J * D * peircePlus J + 0) := by
      rw [h_plus_plus, h_minus_minus]
    _ = peircePlus J * D * peirceMinus J + peirceMinus J * D * peircePlus J := by
      simp only [zero_add, add_zero]

/-! ### Affine Klein maps and their determinant sign -/

/-- Affine glide reflection on $\mathbb{R}^2$: $T_a(x, y) = (x + 1, -y)$. -/
def affineTa : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun p := (p.1 + 1, -p.2)
  invFun p := (p.1 - 1, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- Affine vertical translation on $\mathbb{R}^2$: $T_b(x, y) = (x, y + 1)$. -/
def affineTb : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- Semidirect product relation $a b a^{-1} = b^{-1}$ holds for the affine Klein model. -/
theorem affine_klein_relation :
    affineTa.trans (affineTb.trans affineTa.symm) = affineTb.symm := by
  ext p
  · simp [affineTa, affineTb]
  · simp [affineTa, affineTb]
    ring

/-- The linear part of the glide transformation $T_a$. -/
def linearTa : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- The glide reflection has determinant $-1$, realizing the orientation-reversing $\mathbb{Z}_2$ character. -/
theorem linearTa_det : linearTa.det = -1 := by
  simp [linearTa, Matrix.det_fin_two]

/-- The affine Klein glide's linear part is the diagonal involution `matJ`. -/
theorem linearTa_eq_matJ : linearTa = matJ (R := ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [linearTa, matJ]

/-- Although its determinant is negative, the Klein glide's linear part fixes
the chosen involution `matJ` under conjugation. -/
theorem linearTa_conjugates_matJ :
    linearTa * matJ (R := ℝ) * linearTa = matJ (R := ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [linearTa, matJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The off-diagonal reflection also has determinant `-1`. -/
theorem matK_det : (matK (R := ℝ)).det = -1 := by
  simp [matK, Matrix.det_fin_two]

/-- This different determinant-negative matrix conjugates `matJ` to `-matJ`. -/
theorem matK_conjugates_matJ :
    matK (R := ℝ) * matJ (R := ℝ) * matK (R := ℝ) = -matJ (R := ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matK, matJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem peircePlus_matJ_eq :
    peircePlus (matJ (R := ℝ)) = matPeircePlusJ (R := ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [peircePlus, matJ, matPeircePlusJ]

theorem peirceMinus_matJ_eq :
    peirceMinus (matJ (R := ℝ)) = matPeirceMinusJ (R := ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [peirceMinus, matJ, matPeirceMinusJ]

/-- Conjugation by the affine glide's linear part preserves the positive
Peirce projector for `matJ`. -/
theorem linearTa_preserves_matJ_peircePlus :
    linearTa * peircePlus (matJ (R := ℝ)) * linearTa =
      peircePlus (matJ (R := ℝ)) := by
  rw [peircePlus_matJ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [linearTa, matJ, matPeircePlusJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugation by the affine glide's linear part also preserves the negative
Peirce projector for `matJ`. Thus this affine reflection fixes both eigenspaces
of `matJ`; its negative determinant does not exchange them. -/
theorem linearTa_preserves_matJ_peirceMinus :
    linearTa * peirceMinus (matJ (R := ℝ)) * linearTa =
      peirceMinus (matJ (R := ℝ)) := by
  rw [peirceMinus_matJ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [linearTa, matJ, matPeirceMinusJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugation by the other determinant-negative reflection swaps the
positive and negative `matJ` Peirce projectors. -/
theorem matK_swaps_matJ_peircePlus :
    matK (R := ℝ) * peircePlus (matJ (R := ℝ)) * matK (R := ℝ) =
      peirceMinus (matJ (R := ℝ)) := by
  rw [peircePlus_matJ_eq, peirceMinus_matJ_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matK, matJ, matPeircePlusJ, matPeirceMinusJ,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The sign values satisfy the Klein relator in `Units ℤ`. -/
def kleinSignRelatorCondition (signA signB : Units ℤ) : Prop :=
  signA * signB * signA⁻¹ * signB = 1

/- Every sign assignment satisfies the algebraic group relator. This does not
classify geometric Pin structures. -/
theorem klein_sign_relator_all (signA signB : Units ℤ) :
    kleinSignRelatorCondition signA signB := by
  dsimp [kleinSignRelatorCondition]
  rcases Int.units_eq_one_or signA with ha | ha <;>
  rcases Int.units_eq_one_or signB with hb | hb <;>
  rw [ha, hb] <;> decide

/-- A sign assignment induces a genuine homomorphism from the presented Klein
group to `Units ℤ`. This is an algebraic representation, not a geometric Pin
lift or a classification of Pin structures. -/
def kleinSignRepresentation (signA signB : Units ℤ) :
    _root_.InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup →* Units ℤ :=
  _root_.InfoGeometry.Canonical.KleinPresentedGroup.kleinRep signA signB (by
    have h := klein_sign_relator_all signA signB
    change signA * signB * signA⁻¹ * signB = 1 at h
    calc
      signA * signB * signA⁻¹ =
          (signA * signB * signA⁻¹) * (signB * signB⁻¹) := by simp
      _ = ((signA * signB * signA⁻¹) * signB) * signB⁻¹ := by
        simp [mul_assoc]
      _ = 1 * signB⁻¹ := by rw [h]
      _ = signB⁻¹ := by simp)

theorem kleinSignRepresentation_generators (signA signB : Units ℤ) :
    kleinSignRepresentation signA signB
        (_root_.InfoGeometry.Canonical.KleinPresentedGroup.toKlein
          _root_.InfoGeometry.Canonical.KleinPresentedGroup.genA) = signA ∧
      kleinSignRepresentation signA signB
        (_root_.InfoGeometry.Canonical.KleinPresentedGroup.toKlein
          _root_.InfoGeometry.Canonical.KleinPresentedGroup.genB) = signB :=
  _root_.InfoGeometry.Canonical.KleinPresentedGroup.kleinRep_relator_relation
    signA signB _

def kleinSignRepresentationPP :
    _root_.InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup →* Units ℤ :=
  kleinSignRepresentation 1 1
def kleinSignRepresentationPM :
    _root_.InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup →* Units ℤ :=
  kleinSignRepresentation 1 (-1)
def kleinSignRepresentationMP :
    _root_.InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup →* Units ℤ :=
  kleinSignRepresentation (-1) 1
def kleinSignRepresentationMM :
    _root_.InfoGeometry.Canonical.KleinPresentedGroup.KleinGroup →* Units ℤ :=
  kleinSignRepresentation (-1) (-1)

/-! ### Conditional automorphism action on split projectors -/

/-- An algebra automorphism sending `J` to `-J` swaps the projectors. This is
additional data and does not follow from the orientation character alone. -/
theorem orientation_swap_plus {A : Type*} [Ring A] [Algebra ℝ A]
    (J : A) (σ : A ≃ₐ[ℝ] A) (h_J : σ J = -J) :
    σ (peircePlus J) = peirceMinus J := by
  dsimp [peircePlus, peirceMinus]
  rw [map_smul, map_add, map_one, h_J, ← sub_eq_add_neg]

/-- An algebra automorphism sending `J` to `-J` swaps the projectors. -/
theorem orientation_swap_minus {A : Type*} [Ring A] [Algebra ℝ A]
    (J : A) (σ : A ≃ₐ[ℝ] A) (h_J : σ J = -J) :
    σ (peirceMinus J) = peircePlus J := by
  dsimp [peircePlus, peirceMinus]
  rw [map_smul, map_sub, map_one, h_J, sub_neg_eq_add]

/-- Double traversal restores original polarization: $\sigma^2(P_+) = P_+$. -/
theorem orientation_double_swap_plus {A : Type*} [Ring A] [Algebra ℝ A]
    (J : A) (σ : A ≃ₐ[ℝ] A) (h_J : σ J = -J) :
    σ (σ (peircePlus J)) = peircePlus J := by
  rw [orientation_swap_plus J σ h_J]
  rw [orientation_swap_minus J σ h_J]

/-- Double traversal restores original polarization: $\sigma^2(P_-) = P_-$. -/
theorem orientation_double_swap_minus {A : Type*} [Ring A] [Algebra ℝ A]
    (J : A) (σ : A ≃ₐ[ℝ] A) (h_J : σ J = -J) :
    σ (σ (peirceMinus J)) = peirceMinus J := by
  rw [orientation_swap_minus J σ h_J]
  rw [orientation_swap_plus J σ h_J]

/-! ### Master Synthesis Packet -/

/--
Packet collecting finite split-complex, matrix, projector, and affine-relator
identities. It does not assert a geometric Pin structure or a manifold-level
Dirac-Kähler construction.
-/
structure MasterSplitCayleyDicksonKleinDiracPacket where
  -- Stratum 1: Split-complex Cayley-Dickson
  tau_squared :
    SplitComplex.mul (SplitComplex.tau (R := ℝ)) SplitComplex.tau = SplitComplex.one
  peirce_plus_idempotent :
    SplitComplex.mul (SplitComplex.peirceP (1/2 : ℝ)) (SplitComplex.peirceP (1/2 : ℝ)) =
      SplitComplex.peirceP (1/2 : ℝ)
  peirce_minus_idempotent :
    SplitComplex.mul (SplitComplex.peirceM (1/2 : ℝ)) (SplitComplex.peirceM (1/2 : ℝ)) =
      SplitComplex.peirceM (1/2 : ℝ)
  peirce_orthog :
    SplitComplex.mul (SplitComplex.peirceP (1/2 : ℝ)) (SplitComplex.peirceM (1/2 : ℝ)) =
      SplitComplex.zero
  peirce_resolv :
    SplitComplex.add (SplitComplex.peirceP (1/2 : ℝ)) (SplitComplex.peirceM (1/2 : ℝ)) =
      SplitComplex.one
  zero_divisor_exists :
    SplitComplex.mul (SplitComplex.add SplitComplex.one SplitComplex.tau)
      (SplitComplex.sub SplitComplex.one (SplitComplex.tau (R := ℝ))) = SplitComplex.zero

  -- Stratum 2: Coquaternions H' matrix representation
  coquat_i_sq : matI (R := ℝ) * matI = - matOne
  coquat_j_sq : matJ (R := ℝ) * matJ = matOne
  coquat_k_sq : matK (R := ℝ) * matK = matOne
  coquat_ij : matI (R := ℝ) * matJ = matK
  coquat_ji : matJ (R := ℝ) * matI = - matK

  -- Stratum 3: Matrix Peirce projectors & off-diagonal annihilation
  mat_peirce_plus_sq : matPeircePlusJ (R := ℝ) * matPeircePlusJ = matPeircePlusJ
  mat_peirce_minus_sq : matPeirceMinusJ (R := ℝ) * matPeirceMinusJ = matPeirceMinusJ
  mat_peirce_orthog : matPeircePlusJ (R := ℝ) * matPeirceMinusJ = 0
  mat_peirce_complete : matPeircePlusJ (R := ℝ) + matPeirceMinusJ = matOne

  -- Affine Klein relation and sign-relator checks
  klein_semidirect : affineTa.trans (affineTb.trans affineTa.symm) = affineTb.symm
  linear_ta_det : linearTa.det = -1
  sign_relator_pp : kleinSignRelatorCondition 1 1
  sign_relator_pm : kleinSignRelatorCondition 1 (-1)
  sign_relator_mp : kleinSignRelatorCondition (-1) 1
  sign_relator_mm : kleinSignRelatorCondition (-1) (-1)

/-- Construction of the Master Synthesis Packet. -/
def makeMasterSplitCayleyDicksonKleinDiracPacket :
    MasterSplitCayleyDicksonKleinDiracPacket where
  tau_squared := SplitComplex.tau_sq
  peirce_plus_idempotent := SplitComplex.peirceP_sq (1/2 : ℝ) (by norm_num)
  peirce_minus_idempotent := SplitComplex.peirceM_sq (1/2 : ℝ) (by norm_num)
  peirce_orthog := SplitComplex.peirce_orthogonal (1/2 : ℝ)
  peirce_resolv := SplitComplex.peirce_partition (1/2 : ℝ) (by norm_num)
  zero_divisor_exists := SplitComplex.split_zero_divisor
  coquat_i_sq := coquat_i_sq
  coquat_j_sq := coquat_j_sq
  coquat_k_sq := coquat_k_sq
  coquat_ij := coquat_ij
  coquat_ji := coquat_ji
  mat_peirce_plus_sq := matPeircePlusJ_sq
  mat_peirce_minus_sq := matPeirceMinusJ_sq
  mat_peirce_orthog := matPeirce_orthog
  mat_peirce_complete := matPeirce_complete
  klein_semidirect := affine_klein_relation
  linear_ta_det := linearTa_det
  sign_relator_pp := klein_sign_relator_all 1 1
  sign_relator_pm := klein_sign_relator_all 1 (-1)
  sign_relator_mp := klein_sign_relator_all (-1) 1
  sign_relator_mm := klein_sign_relator_all (-1) (-1)

end InfoGeometry.Canonical.MasterSplitCayleyDicksonKleinDirac
