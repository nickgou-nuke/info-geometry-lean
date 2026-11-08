import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import InfoGeometry.Clifford.CockleCoquaternionPlanarTriad
import InfoGeometry.Clifford.SolderingIsotropicSouriauSheetBridge
import InfoGeometry.Clifford.ConformalProjectiveBoundaryCasimirBridge
import InfoGeometry.Clifford.KleinBottleLoxodromicTwistCPTBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

/-!
# LogCFT de Rham Cohomology, Log-Potential, and Chiral Apex Frame Dragging

Module: `InfoGeometry.Clifford.LogCFTDeRhamApexMonodromyBridge`

This module formalizes:
1. **The Split-Quaternion Carrier and Parabolic Lightcone Nilpotents**:
   - In Cockle's coquaternion algebra $\mathbb{H}_{\mathrm{split}} \cong \mathrm{Cl}(1,1)$:
     - Upper parabolic element $N_{\mathrm{upper}} = -e_2 - \omega$: $N_{\mathrm{upper}}^2 = 0$.
     - Lower parabolic element $N_{\mathrm{lower}} = -e_2 + \omega$: $N_{\mathrm{lower}}^2 = 0$.
     - Under matrix representation $\Psi$:
       $\Psi(N_{\mathrm{upper}}) = 2 N$, $\Psi(N_{\mathrm{lower}}) = -2 N^\top$.
   - In the real matrix algebra $M_2(R)$:
     - $N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$ satisfies $N^2 = 0$, $\operatorname{Tr}(N) = 0$, and $\det_2(N) = 0$.
     - $N^\top = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$ satisfies $(N^\top)^2 = 0$.

2. **Chiral Ladder Projection on the Causal Lightcone**:
   - Chiral projectors: $P_L = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}$ and
     $P_R = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}$.
   - $P_L N = N$, $N P_R = N$, $P_R N = 0$, $N P_L = 0$.
   - Two-sided chiral decomposition: $P_L N P_R = N$.
   - $N$ acts as a nilpotent ladder operator dragging states across the chiral split from the
     right chiral sheet $P_R$ to the left chiral sheet $P_L$.

3. **Log-Potential de Rham Monodromy Group and Linear Winding**:
   - Unipotent parallel transport operator:
     $$\mathcal{M}(c) = \mathbf{1} + c N = \begin{pmatrix} 1 & c \\ 0 & 1 \end{pmatrix} \in \mathrm{SL}_2(R)$$
   - Additive group law: $\mathcal{M}(c_1) \mathcal{M}(c_2) = \mathcal{M}(c_1 + c_2)$.
   - Linear de Rham winding power law: $\mathcal{M}(c)^k = \mathcal{M}(k \cdot c) = \mathbf{1} + (k \cdot c) N$ for all $k \in \mathbb{N}$.
   - Exact determinant conservation: $\det_2(\mathcal{M}(c)) = 1$ and $\det_2(\mathcal{M}(c)^k) = 1$.
   - Inverse: $\mathcal{M}(c) \mathcal{M}(-c) = \mathbf{1}$.

4. **Frame Dragging around the Apex of the Chiral Causal Lightcone**:
   - Frame dragging action on vectors and frames: $\operatorname{dragFrame}(c, F) = \mathcal{M}(c) F$.
   - Congruence action on the Minkowski soldering matrix:
     $$\operatorname{dragSoldering}(c, X) = \mathcal{M}(c) X \mathcal{M}(c)^\top$$
   - Apex invariance: $\operatorname{dragSoldering}(c, 0) = 0$ (the lightcone apex is the fixed center).
   - Invariance of the conformal Casimir / Minkowski metric interval:
     $$\det_2(\operatorname{dragSoldering}(c, X(t, x, y, z))) = \det_2(X(t, x, y, z)) = t^2 - x^2 + y^2 - z^2$$
   - Invariance of the left chiral Souriau sheet: $\operatorname{dragSoldering}(c, P_L) = P_L$.
   - Parabolic shear on the right chiral Souriau sheet: $\operatorname{dragSoldering}(c, P_R) = \begin{pmatrix} c^2 & c \\ c & 1 \end{pmatrix}$ with $\det_2 = 0$.

5. **Intertwining with Klein Parity Inversion**:
   - Conjugation by the Klein reflection matrix $e_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$:
     $$e_1 N e_1 = N^\top, \qquad e_1 \mathcal{M}(c) e_1 = \mathcal{M}(c)^\top = \mathbf{1} + c N^\top$$
   - Reversal of chiral frame dragging under Klein parity: swaps upper-triangular (leftward)
     monodromy into lower-triangular (rightward) monodromy.

6. **Complex LogCFT Monodromy Decomposition (General $h \in \mathbb{C}$)**:
   - For conformal weight $h \in \mathbb{C}$:
     $$\mathcal{M}_{\mathbb{C}}(h, c) = \exp(2\pi i h) (\mathbf{1} + c N)$$
   - Determinant: $\det_2(\mathcal{M}_{\mathbb{C}}(h, c)) = \exp(4\pi i h)$.
   - For $h = 0$, $\det_2 = 1$, recovering the real unipotent frame dragging.

All proofs are native Mathlib with 0 sorry, 0 admit, and 0 custom axioms.
-/

namespace InfoGeometry.Clifford.LogCFTApex

open Matrix
open InfoGeometry.Clifford.Coquaternion
open InfoGeometry.Clifford.SolderingIsotropic

/-- The $2 \times 2$ matrix algebra over a ring $R$. -/
abbrev Mat2 (R : Type*) := Matrix (Fin 2) (Fin 2) R

/-- Determinant of a $2 \times 2$ matrix. -/
def det2 {R : Type*} [CommRing R] (M : Mat2 R) : R :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- Determinant of the transpose of a $2 \times 2$ matrix. -/
theorem det2_transpose {R : Type*} [CommRing R] (M : Mat2 R) :
    det2 Mᵀ = det2 M := by
  simp [det2, Matrix.transpose]
  ring

/-- Multiplicativity of the $2 \times 2$ determinant. -/
theorem det2_mul {R : Type*} [CommRing R] (A B : Mat2 R) :
    det2 (A * B) = det2 A * det2 B := by
  simp [det2, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Determinant under scalar multiplication. -/
theorem det2_smul {R : Type*} [CommRing R] (k : R) (M : Mat2 R) :
    det2 (k • M) = k ^ 2 * det2 M := by
  simp [det2]
  ring

/-- The parity reflection matrix $e_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix} \in M_2(R)$. -/
def parity_e1 {R : Type*} [CommRing R] : Mat2 R :=
  KleinBottleLoxodromicTwist.e1

section RingCarrier

variable {R : Type*} [CommRing R]

/-! ### 1. Split-Quaternion Parabolic Generators and Matrix Nilpotency -/

/-- The upper parabolic generator in Cockle's coquaternion algebra:
    $N_{\mathrm{upper}} = -e_2 - \omega = \langle 0, 0, -1, -1 \rangle$. -/
def coquaternion_N_upper : Coquaternion R :=
  ⟨0, 0, -1, -1⟩

/-- The lower parabolic generator in Cockle's coquaternion algebra:
    $N_{\mathrm{lower}} = -e_2 + \omega = \langle 0, 0, -1, 1 \rangle$. -/
def coquaternion_N_lower : Coquaternion R :=
  ⟨0, 0, -1, 1⟩

/-- $N_{\mathrm{upper}}$ squares to zero in $\mathbb{H}_{\mathrm{split}}$:
    $(-e_2 - \omega)^2 = e_2^2 + e_2 \omega + \omega e_2 + \omega^2 = -1 + e_1 - e_1 + 1 = 0$. -/
theorem coquaternion_N_upper_sq :
    (coquaternion_N_upper : Coquaternion R) * coquaternion_N_upper = 0 := by
  ext <;> { simp [coquaternion_N_upper]; try ring }

/-- $N_{\mathrm{lower}}$ squares to zero in $\mathbb{H}_{\mathrm{split}}$:
    $(-e_2 + \omega)^2 = e_2^2 - e_2 \omega - \omega e_2 + \omega^2 = -1 - e_1 + e_1 + 1 = 0$. -/
theorem coquaternion_N_lower_sq :
    (coquaternion_N_lower : Coquaternion R) * coquaternion_N_lower = 0 := by
  ext <;> { simp [coquaternion_N_lower]; try ring }

/-- The standard upper nilpotent shear matrix $N \in M_2(R)$:
    $N = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$. -/
def N : Mat2 R :=
  !![ 0, 1;
      0, 0 ]

/-- Explicit coordinate form of the transpose nilpotent matrix:
    $N^\top = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$. -/
theorem N_transpose_eq : (N : Mat2 R)ᵀ = !![ 0, 0; 1, 0 ] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- The matrix representation of $N_{\mathrm{upper}}$ is $2 \cdot N$:
    $\Psi(N_{\mathrm{upper}}) = \begin{pmatrix} 0 & 2 \\ 0 & 0 \end{pmatrix} = 2 N$. -/
theorem toMatrix_coquaternion_N_upper :
    Coquaternion.toMatrix (coquaternion_N_upper : Coquaternion R) = (2 : R) • (N : Mat2 R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Coquaternion.toMatrix, coquaternion_N_upper, N]
    try ring
  }

/-- The matrix representation of $N_{\mathrm{lower}}$ is $-2 \cdot N^\top$:
    $\Psi(N_{\mathrm{lower}}) = \begin{pmatrix} 0 & 0 \\ -2 & 0 \end{pmatrix} = -2 N^\top$. -/
theorem toMatrix_coquaternion_N_lower :
    Coquaternion.toMatrix (coquaternion_N_lower : Coquaternion R) = (-2 : R) • (N : Mat2 R)ᵀ := by
  rw [N_transpose_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Coquaternion.toMatrix, coquaternion_N_lower]
    try ring
  }

/-- $N$ is nilpotent of order 2: $N^2 = 0$. -/
@[simp]
theorem N_sq_zero : (N : Mat2 R) * N = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_two]

/-- The transpose $N^\top$ is nilpotent of order 2: $(N^\top)^2 = 0$. -/
@[simp]
theorem N_transpose_sq_zero : (N : Mat2 R)ᵀ * Nᵀ = 0 := by
  rw [N_transpose_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Tracelessness of $N$: $\operatorname{Tr}(N) = 0$. -/
@[simp]
theorem trace_N : (N : Mat2 R) 0 0 + (N : Mat2 R) 1 1 = 0 := by
  simp [N]

/-- Determinant of $N$ is zero: $\det_2(N) = 0$ (lies on the null lightcone). -/
@[simp]
theorem det2_N : det2 (N : Mat2 R) = 0 := by
  simp [det2, N]

/-- Determinant of $N^\top$ is zero: $\det_2(N^\top) = 0$. -/
@[simp]
theorem det2_N_transpose : det2 ((N : Mat2 R)ᵀ) = 0 := by
  rw [N_transpose_eq]
  simp [det2]

/-! ### 2. Chiral Ladder Projections on the Lightcone -/

/-- Left chiral projector absorbs $N$ on the left: $P_L N = N$. -/
@[simp]
theorem P_L_mul_N : (P_L : Mat2 R) * N = N := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_L, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Right chiral projector absorbs $N$ on the right: $N P_R = N$. -/
@[simp]
theorem N_mul_P_R : (N : Mat2 R) * P_R = N := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_R, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Right chiral projector annihilates $N$ on the left: $P_R N = 0$. -/
@[simp]
theorem P_R_mul_N : (P_R : Mat2 R) * N = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_R, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Left chiral projector annihilates $N$ on the right: $N P_L = 0$. -/
@[simp]
theorem N_mul_P_L : (N : Mat2 R) * P_L = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_L, N, Matrix.mul_apply, Fin.sum_univ_two]

/-- Two-sided chiral decomposition: $N = P_L N P_R$.
    $N$ acts as a chiral transition ladder from the right sheet $P_R$ to the left sheet $P_L$. -/
theorem chiral_ladder_decomp :
    (P_L : Mat2 R) * N * P_R = N := by
  rw [P_L_mul_N, N_mul_P_R]

/-- Transpose chiral ladder decomposition: $N^\top = P_R N^\top P_L$. -/
theorem chiral_ladder_transpose_decomp :
    (P_R : Mat2 R) * Nᵀ * P_L = Nᵀ := by
  rw [N_transpose_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [P_L, P_R, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### 3. Log-Potential de Rham Monodromy and Linear Winding -/

/-- The unipotent monodromy operator $\mathcal{M}(c) = \mathbf{1} + c N = \begin{pmatrix} 1 & c \\ 0 & 1 \end{pmatrix}$. -/
def monodromy (c : R) : Mat2 R :=
  1 + c • N

/-- Coordinate form of the monodromy operator:
    $\mathcal{M}(c) = \begin{pmatrix} 1 & c \\ 0 & 1 \end{pmatrix}$. -/
theorem monodromy_coords (c : R) :
    monodromy c = !![ 1, c;
                     0, 1 ] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [monodromy, N]

/-- Identity at parameter zero: $\mathcal{M}(0) = \mathbf{1}$. -/
@[simp]
theorem monodromy_zero : monodromy (0 : R) = 1 := by
  simp [monodromy]

/-- Additive group law of parallel transport monodromy:
    $\mathcal{M}(c_1) \mathcal{M}(c_2) = \mathcal{M}(c_1 + c_2)$. -/
theorem monodromy_mul (c₁ c₂ : R) :
    monodromy c₁ * monodromy c₂ = monodromy (c₁ + c₂) := by
  rw [monodromy_coords, monodromy_coords, monodromy_coords]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- Linear winding power law for LogCFT de Rham monodromy:
    $(\mathcal{M}(c))^k = \mathcal{M}(k \cdot c) = \mathbf{1} + (k \cdot c) N$ for all $k \in \mathbb{N}$. -/
theorem monodromy_pow (k : ℕ) (c : R) :
    (monodromy c) ^ k = monodromy ((k : R) * c) := by
  induction k with
  | zero =>
      simp [monodromy_zero]
  | succ n ih =>
      rw [pow_succ, ih, monodromy_mul]
      congr 1
      push_cast
      ring

/-- Inverse monodromy: $\mathcal{M}(c) \mathcal{M}(-c) = \mathbf{1}$. -/
@[simp]
theorem monodromy_mul_inv (c : R) :
    monodromy c * monodromy (-c) = 1 := by
  rw [monodromy_mul, add_neg_cancel, monodromy_zero]

/-- Inverse monodromy on the left: $\mathcal{M}(-c) \mathcal{M}(c) = \mathbf{1}$. -/
@[simp]
theorem monodromy_inv_mul (c : R) :
    monodromy (-c) * monodromy c = 1 := by
  rw [monodromy_mul, neg_add_cancel, monodromy_zero]

/-- Determinant of the monodromy operator is strictly 1:
    $\det_2(\mathcal{M}(c)) = 1 \cdot 1 - c \cdot 0 = 1$.
    Thus $\mathcal{M}(c) \in \mathrm{SL}_2(R)$ is an exact unipotent parabolic flow. -/
@[simp]
theorem det2_monodromy (c : R) :
    det2 (monodromy c) = 1 := by
  rw [monodromy_coords]
  simp [det2]

/-- Determinant of any winding power is strictly 1: $\det_2(\mathcal{M}(c)^k) = 1$. -/
@[simp]
theorem det2_monodromy_pow (k : ℕ) (c : R) :
    det2 ((monodromy c) ^ k) = 1 := by
  rw [monodromy_pow, det2_monodromy]

/-! ### 4. Frame Dragging around the Apex of the Chiral Causal Lightcone -/

/-- Frame dragging of a general frame matrix $F \in M_2(R) by parameter $c$:
    $\operatorname{dragFrame}(c, F) = \mathcal{M}(c) F$. -/
def dragFrame (c : R) (F : Mat2 R) : Mat2 R :=
  monodromy c * F

/-- Congruence action of the frame dragging on the spacetime soldering matrix $X$:
    $\operatorname{dragSoldering}(c, X) = \mathcal{M}(c) X \mathcal{M}(c)^\top$. -/
def dragSoldering (c : R) (X : Mat2 R) : Mat2 R :=
  monodromy c * X * (monodromy c)ᵀ

/-- Transpose of the monodromy operator:
    $(\mathcal{M}(c))^\top = \mathbf{1} + c N^\top = \begin{pmatrix} 1 & 0 \\ c & 1 \end{pmatrix}$. -/
theorem monodromy_transpose (c : R) :
    (monodromy c)ᵀ = 1 + c • (N : Mat2 R)ᵀ := by
  simp only [monodromy, transpose_add, transpose_one, transpose_smul]

/-- Coordinate form of the transpose monodromy operator:
    $(\mathcal{M}(c))^\top = \begin{pmatrix} 1 & 0 \\ c & 1 \end{pmatrix}$. -/
theorem monodromy_transpose_coords (c : R) :
    (monodromy c)ᵀ = !![ 1, 0;
                        c, 1 ] := by
  rw [monodromy_coords]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.transpose]

/-- Determinant of the transpose monodromy is strictly 1:
    $\det_2((\mathcal{M}(c))^\top) = 1$. -/
@[simp]
theorem det2_monodromy_transpose (c : R) :
    det2 ((monodromy c)ᵀ) = 1 := by
  rw [det2_transpose, det2_monodromy]

/-- At the apex of the causal lightcone ($X = 0$), the frame dragging fixes the apex:
    $\operatorname{dragSoldering}(c, 0) = 0$. -/
@[simp]
theorem dragSoldering_apex (c : R) :
    dragSoldering c (0 : Mat2 R) = 0 := by
  simp [dragSoldering]

/-- Conservation of the Minkowski / conformal Casimir interval under frame dragging:
    For any spacetime matrix $X$, $\det_2(\operatorname{dragSoldering}(c, X)) = \det_2(X)$. -/
theorem det2_dragSoldering_matrix (c : R) (X : Mat2 R) :
    det2 (dragSoldering c X) = det2 X := by
  simp [dragSoldering, det2_mul, det2_monodromy, det2_monodromy_transpose]

/-- Conservation of the physical Minkowski metric interval for $X(t, x, y, z)$:
    $$\det_2(\operatorname{dragSoldering}(c, X(t, x, y, z))) = t^2 - x^2 + y^2 - z^2$$ -/
theorem det2_dragSoldering (c : R) (t x y z : R) :
    det2 (dragSoldering c (solderingMatrix t x y z)) = t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2 := by
  rw [det2_dragSoldering_matrix]
  simp [det2, solderingMatrix]
  ring

/-- Explicit sheared coordinate entries of the dragged soldering matrix:
    $$\operatorname{dragSoldering}(c, X(t, x, y, z)) =
      \begin{pmatrix} (t+z) + c(x+y) + c(x-y + c(t-z)) & (x-y) + c(t-z) \\
                      (x+y) + c(t-z) & t-z \end{pmatrix}$$ -/
theorem dragSoldering_coords (c : R) (t x y z : R) :
    dragSoldering c (solderingMatrix t x y z) =
    !![ (t + z) + c * (x + y) + c * ((x - y) + c * (t - z)), (x - y) + c * (t - z);
        (x + y) + c * (t - z),                                t - z ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [dragSoldering, monodromy_coords, Matrix.transpose, solderingMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- Invariance of the left chiral Souriau sheet under apex frame dragging:
    $\operatorname{dragSoldering}(c, P_L) = P_L$.
    The left chiral null generator along the lightcone is strictly an invariant ray! -/
theorem dragSoldering_P_L (c : R) :
    dragSoldering c P_L = P_L := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [dragSoldering, monodromy_coords, Matrix.transpose, P_L, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- Action on the right chiral Souriau sheet under apex frame dragging:
    $\operatorname{dragSoldering}(c, P_R) = \begin{pmatrix} c^2 & c \\ c & 1 \end{pmatrix}$. -/
theorem dragSoldering_P_R (c : R) :
    dragSoldering c P_R = !![ c^2, c;
                              c,   1 ] := by
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [dragSoldering, monodromy_coords, Matrix.transpose, P_R, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- The dragged right chiral state remains strictly on the null cone:
    $\det_2(\operatorname{dragSoldering}(c, P_R)) = 0$. -/
theorem det2_dragSoldering_P_R (c : R) :
    det2 (dragSoldering c P_R) = 0 := by
  rw [dragSoldering_P_R]
  simp [det2]
  ring

/-! ### 5. Intertwining with Klein Parity Inversion -/

/-- Conjugation of the nilpotent generator $N$ by the Klein reflection matrix $e_1$:
    $$e_1 N e_1 = N^\top$$
    The Klein parity reflection exchanges the upper nilpotent shear with the lower nilpotent shear. -/
theorem e1_N_conj :
    parity_e1 * N * parity_e1 = (N : Mat2 R)ᵀ := by
  rw [N_transpose_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [parity_e1, KleinBottleLoxodromicTwist.e1, N, Matrix.mul_apply, Fin.sum_univ_two]
  }

/-- Conjugation of the lower nilpotent $N^\top$ by $e_1$ restores $N$:
    $$e_1 N^\top e_1 = N$$ -/
theorem e1_N_transpose_conj :
    parity_e1 * (N : Mat2 R)ᵀ * parity_e1 = N := by
  rw [N_transpose_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [parity_e1, KleinBottleLoxodromicTwist.e1, N, Matrix.mul_apply, Fin.sum_univ_two]
  }

/-- Reversal of chiral frame dragging under Klein parity:
    Conjugating the monodromy operator $\mathcal{M}(c)$ by $e_1$ yields the transpose monodromy:
    $$e_1 \mathcal{M}(c) e_1 = (\mathcal{M}(c))^\top = \mathbf{1} + c N^\top$$ -/
theorem e1_monodromy_conj (c : R) :
    parity_e1 * monodromy c * parity_e1 = (monodromy c)ᵀ := by
  rw [monodromy_transpose_coords]
  ext i j
  fin_cases i <;> fin_cases j <;> {
    simp [parity_e1, KleinBottleLoxodromicTwist.e1, monodromy_coords, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- Klein-reflected monodromy matrix coordinates:
    $e_1 \mathcal{M}(c) e_1 = \begin{pmatrix} 1 & 0 \\ c & 1 \end{pmatrix}$. -/
theorem e1_monodromy_conj_coords (c : R) :
    parity_e1 * monodromy c * parity_e1 = !![ 1, 0;
                                              c, 1 ] := by
  rw [e1_monodromy_conj, monodromy_transpose_coords]

end RingCarrier

/-! ### 6. Complex LogCFT Monodromy Decomposition (General $h \in \mathbb{C}$) -/

section ComplexMonodromy

/-- The complex logarithmic CFT monodromy operator with conformal weight $h \in \mathbb{C}$
    and logarithmic shear parameter $c \in \mathbb{C}$:
    $$\mathcal{M}_{\mathbb{C}}(h, c) = \exp(2\pi i h) \cdot (\mathbf{1} + c N)$$ -/
noncomputable def complexMonodromy (h c : ℂ) : Mat2 ℂ :=
  Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * h) • (monodromy c : Mat2 ℂ)

/-- For conformal weight $h = 0$, the complex monodromy recovers the unipotent monodromy:
    $\mathcal{M}_{\mathbb{C}}(0, c) = \mathcal{M}(c)$. -/
@[simp]
theorem complexMonodromy_zero_weight (c : ℂ) :
    complexMonodromy 0 c = monodromy c := by
  dsimp [complexMonodromy]
  have h0 : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * 0 = 0 := by ring
  rw [h0, Complex.exp_zero, one_smul]

/-- Determinant of the complex LogCFT monodromy operator:
    $$\det_2(\mathcal{M}_{\mathbb{C}}(h, c)) = \exp(4\pi i h)$$
    Independent of the shear parameter $c$, and strictly equal to $1$ for $h = 0$. -/
theorem det2_complexMonodromy (h c : ℂ) :
    det2 (complexMonodromy h c) = Complex.exp ((4 : ℂ) * (Real.pi : ℂ) * Complex.I * h) := by
  dsimp [complexMonodromy]
  rw [det2_smul, det2_monodromy, mul_one]
  rw [sq, ← Complex.exp_add]
  congr 1
  ring

/-- At $h = 0$, the complex LogCFT monodromy is unimodular:
    $\det_2(\mathcal{M}_{\mathbb{C}}(0, c)) = 1$. -/
@[simp]
theorem det2_complexMonodromy_zero_weight (c : ℂ) :
    det2 (complexMonodromy 0 c) = 1 := by
  rw [det2_complexMonodromy]
  have h0 : (4 : ℂ) * (Real.pi : ℂ) * Complex.I * 0 = 0 := by ring
  rw [h0, Complex.exp_zero]

end ComplexMonodromy

/-! ### 7. Master Verification Certificate -/

/-- Master verification certificate for LogCFT de Rham cohomology, log-potential,
    and apex frame dragging in the split-quaternion carrier geometry algebra. -/
structure LogCFTDeRhamApexMonodromyBridgeCertificate : Prop where
  coquaternion_nilpotents :
    ∀ (R : Type) [CommRing R],
      ((coquaternion_N_upper : Coquaternion R) * coquaternion_N_upper = 0) ∧
      ((coquaternion_N_lower : Coquaternion R) * coquaternion_N_lower = 0)
  matrix_nilpotency :
    ∀ (R : Type) [CommRing R],
      ((N : Mat2 R) * N = 0) ∧
      ((N : Mat2 R)ᵀ * Nᵀ = 0) ∧
      (det2 (N : Mat2 R) = 0)
  chiral_ladder :
    ∀ (R : Type) [CommRing R],
      ((P_L : Mat2 R) * N * P_R = N) ∧
      ((P_R : Mat2 R) * N = 0) ∧
      ((N : Mat2 R) * P_L = 0)
  unipotent_monodromy_group :
    ∀ (R : Type) [CommRing R] (c₁ c₂ : R),
      monodromy c₁ * monodromy c₂ = monodromy (c₁ + c₂)
  linear_winding_power :
    ∀ (R : Type) [CommRing R] (k : ℕ) (c : R),
      (monodromy c) ^ k = monodromy ((k : R) * c)
  unimodular_monodromy :
    ∀ (R : Type) [CommRing R] (c : R),
      det2 (monodromy c) = 1
  apex_invariance :
    ∀ (R : Type) [CommRing R] (c : R),
      dragSoldering c (0 : Mat2 R) = 0
  minkowski_interval_preservation :
    ∀ (R : Type) [CommRing R] (c : R) (t x y z : R),
      det2 (dragSoldering c (solderingMatrix t x y z)) = t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2
  chiral_ray_invariance :
    ∀ (R : Type) [CommRing R] (c : R),
      dragSoldering c (P_L : Mat2 R) = P_L
  klein_parity_reversal :
    ∀ (R : Type) [CommRing R] (c : R),
      parity_e1 * monodromy c * parity_e1 = (monodromy c)ᵀ
  complex_monodromy_det :
    ∀ (h c : ℂ),
      det2 (complexMonodromy h c) = Complex.exp ((4 : ℂ) * (Real.pi : ℂ) * Complex.I * h)

/-- Master certification theorem: LogCFT de Rham apex monodromy bridge is fully proved. -/
theorem compile_logcft_derham_apex_monodromy_bridge :
    LogCFTDeRhamApexMonodromyBridgeCertificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R _
    exact ⟨coquaternion_N_upper_sq, coquaternion_N_lower_sq⟩
  · intro R _
    exact ⟨N_sq_zero, N_transpose_sq_zero, det2_N⟩
  · intro R _
    exact ⟨chiral_ladder_decomp, P_R_mul_N, N_mul_P_L⟩
  · intro R _ c₁ c₂
    exact monodromy_mul c₁ c₂
  · intro R _ k c
    exact monodromy_pow k c
  · intro R _ c
    exact det2_monodromy c
  · intro R _ c
    exact dragSoldering_apex c
  · intro R _ c t x y z
    exact det2_dragSoldering c t x y z
  · intro R _ c
    exact dragSoldering_P_L c
  · intro R _ c
    exact e1_monodromy_conj c
  · intro h c
    exact det2_complexMonodromy h c

end InfoGeometry.Clifford.LogCFTApex
