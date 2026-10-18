/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge
import InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge

/-!
# Shirokov's Ternary Clifford Algebra $C\ell_2^{\frac{1}{3}}$, Basis-Free Cubic Determinant & Inverse, and $\mathfrak{su}(3)$ Gell-Mann Color Realization (`arXiv:2504.19689`)

This module formalizes the core algebraic and Lie-theoretic theorems of D. Shirokov,
*"On Unitary Groups in Ternary and Generalized Clifford Algebras"* (`arXiv:2504.19689`),
and bridges them to the repository's quadratic Shirokov trace/determinant/inverse module
(`ShirokovCliffordTraceDetInverseBridge.lean`) and Peirce $\mathfrak{sl}_3$ color action
(`RealPeirceG2ColorActionBridge.lean`):

1. **Section 1 — Sylvester Shift ($P$) & Clock ($R(\omega)$) Realization of the Ternary Clifford Algebra $C\ell_2^{\frac{1}{3}} \cong \operatorname{Mat}(3, \mathbb{C})$**:
   - Defines the $3 \times 3$ shift matrix `ternaryShiftP` ($P$) and clock matrix `ternaryClockR ω`
     ($R(\omega) = \operatorname{diag}(1, \omega, \omega^2)$) for a primitive cube root of unity
     $\omega \in \mathbb{C}$ satisfying $\omega^2 + \omega + 1 = 0$.
   - Proves $\omega^3 = 1$ (`omega_cube_eq_one`), $P^3 = I_3$ (`ternaryShiftP_cube`),
     $R(\omega)^3 = I_3$ (`ternaryClockR_cube`), and the Weyl–Sylvester–Morris–Shirokov
     $\omega$-commutation relation $P R(\omega) = \omega R(\omega) P$
     (`ternaryShiftP_mul_ternaryClockR_comm`, Eq. 2.51 / 3.48 of `arXiv:2504.19689`).
2. **Section 2 — Basis-Free Grade-0 Projection $\langle U \rangle_0 = \frac{1}{3}\operatorname{tr}(U)$, Cyclic Symmetry, and Unitary Hermitian Conjugation (Theorem 5.1 & Lemma 7.1)**:
   - Defines `ternaryShirokovGrade0 U = (1 / 3) * Matrix.trace U` and proves rank-0 scalar
     extraction `ternaryShirokovGrade0_multivector` across all 9 ternary basis monomials
     $e_1^j e_2^k$ ($j, k \in \{0, 1, 2\}$) and cyclic symmetry `ternaryShirokovGrade0_mul_comm`
     (Corollary 7.2).
   - Proves Theorem 5.1 generator unitarity: $P^{\mathrm{H}} = P^2 = P^{-1}$
     (`ternaryShiftP_conjTranspose_eq_sq`) and $R(\omega)^{\mathrm{H}} = R(\omega)^2 = R(\omega)^{-1}$
     (`ternaryClockR_conjTranspose_eq_sq`) when $\bar{\omega} = \omega^2$.
3. **Section 3 — Shirokov's Flattening Operator $\underline{U} = 2\langle U \rangle_0 I_3 - U$, Characteristic Polynomial Coefficients $(C_{(1)}, C_{(2)}, C_{(3)})$, Adjugate, and Matrix-Free Inverse in $C\ell_2^{\frac{1}{3}}$ (Theorems 7.5 & 7.7, Corollary 7.6)**:
   - Defines `ternaryUnderline U = (2 * ternaryShirokovGrade0 U) • 1 - U` (Eq. 7.61) and proves
     all five identities of Theorem 7.7: involutivity $\underline{\underline{U}} = U$,
     linearity, shift invariance $\underline{U V} U = U \underline{V U}$, nested flattening
     $\underline{U \underline{V}} = \underline{U}\,\underline{V} + \underline{U} V - \underline{U V}$,
     and self-flattening $\underline{U \underline{U}} = (\underline{U})^2 + \underline{U} U - \underline{U^2}$.
   - Defines Shirokov's basis-free adjugate `ternaryShirokovAdjugate U` (Eq. 8.25) and proves its
     flattened form (Eq. 8.36), Faddeev–LeVerrier expansion (Eq. 7.53), exact cubic determinant
     identity $U \cdot \operatorname{Adj}(U) = \det(U) I_3 = \operatorname{Adj}(U) \cdot U$
     (`ternaryShirokov_adjugate_mul_eq_det`, Eq. 8.29), and explicit matrix-free two-sided inverse
     (`ternaryShirokov_inverse_formula`, Corollary 7.6 & Eq. 8.21).
4. **Section 4 — Special Unitary Lie Algebra $\mathfrak{su}C\ell_2^{\frac{1}{3}} \cong \mathfrak{su}(3)$ and Transition to the 8 Gell-Mann Color Generators (Section 8, Eqs. 8.83–8.1025)**:
   - Proves that the skew-Hermitian grade-0-traceless subspace `IsTernarySU3LieElement` is closed
     under the Lie commutator $\lbrack X, Y \rbrack = X Y - Y X$ (`ternarySU3LieElement_commutator`).
   - Formalizes Shirokov's ternary Clifford $\mathfrak{su}(3)$ basis elements $\beta_1, \dots, \beta_8$
     and the anti-Hermitian Gell-Mann generators $\theta_1, \dots, \theta_8$ ($\theta_j = i \lambda_j$),
     proving the explicit bidirectional change-of-basis laws (Eqs. 1009–1024).
5. **Section 5 — Master Synthesis Theorem (`shirokov_ternary_clifford_unitary_su3_grand_synthesis`)**:
   - Unites the quadratic ($\mathrm{Cl}(1,1), \mathrm{Cl}(2,2)$) and ternary ($C\ell_2^{\frac{1}{3}}$)
     Shirokov trace/determinant/inverse theorems with the $\mathfrak{su}(3)$ Gell-Mann color transition
     and the real Peirce $\mathfrak{sl}_3(\mathbb{R})$ color action.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix
open Matrix
open InfoGeometry.Synthesis.ShirokovCliffordTraceDetInverseBridge
open InfoGeometry.Synthesis.RealPeirceG2ColorActionBridge
open InfoGeometry.Synthesis.Cl55SuperGrassmannianKKTSynthesis
open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis

namespace InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis

/-!
## Section 1: Sylvester Shift ($P$) & Clock ($R(\omega)$) Realization of $C\ell_2^{\frac{1}{3}} \cong \operatorname{Mat}(3, \mathbb{C})$
-/

/-- Sylvester cyclic shift matrix
$P = \beta(e_1) = \begin{pmatrix} 0 & 1 & 0 \\ 0 & 0 & 1 \\ 1 & 0 & 0 \end{pmatrix} \in M_3(\mathbb{C})$
(Eq. 3.10 / 3.86 of `arXiv:2504.19689`). -/
def ternaryShiftP : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0;
     0, 0, 1;
     1, 0, 0]

/-- Sylvester clock matrix
$R(\omega) = \beta(e_2) = \operatorname{diag}(1, \omega, \omega^2) \in M_3(\mathbb{C})$
(Eq. 3.41 / 3.93 of `arXiv:2504.19689`). -/
def ternaryClockR (ω : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, ω, 0;
     0, 0, ω ^ 2]

/-- Evaluated clock matrix $R(0) = \operatorname{diag}(1, 0, 0) \in M_3(\mathbb{C})$. -/
def ternaryClockR0 : Matrix (Fin 3) (Fin 3) ℂ :=
  ternaryClockR 0

/-- The cyclic shift matrix $P$ and the diagonal rank-1 clock projector $R(0)$ do not commute in $M_3(\mathbb{C})$:
`ternaryShiftP * ternaryClockR0 ≠ ternaryClockR0 * ternaryShiftP`. -/
theorem ternaryShiftP_mul_ternaryClockR_zero_ne_comm :
    ternaryShiftP * ternaryClockR0 ≠ ternaryClockR0 * ternaryShiftP := by
  intro h_comm
  have h01 : (ternaryShiftP * ternaryClockR0) 0 1 = (ternaryClockR0 * ternaryShiftP) 0 1 :=
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) h_comm
  revert h01
  simp [ternaryShiftP, ternaryClockR0, ternaryClockR, Matrix.mul_apply, Fin.sum_univ_three]

/-- Any primitive cube root of unity $\omega \in \mathbb{C}$ satisfying the cyclotomic polynomial
$\omega^2 + \omega + 1 = 0$ satisfies $\omega^3 = 1$ (Eq. 2.55 of `arXiv:2504.19689`). -/
theorem omega_cube_eq_one (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 3 = 1 := by
  calc
    ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
    _ = (ω - 1) * 0 + 1 := by rw [hω]
    _ = 1 := by ring

/-- The shift generator $P = \beta(e_1)$ satisfies the ternary Clifford relation $P^3 = I_3$
(Eq. 2.50 / 3.37 of `arXiv:2504.19689`). -/
theorem ternaryShiftP_cube :
    ternaryShiftP ^ 3 = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [pow_succ, pow_zero, ternaryShiftP, Matrix.mul_apply, Fin.sum_univ_three])

/-- The clock generator $R(\omega) = \beta(e_2)$ satisfies the ternary Clifford relation
$R(\omega)^3 = I_3$ whenever $\omega^2 + \omega + 1 = 0$ (Eq. 2.50 / 3.48 of `arXiv:2504.19689`). -/
theorem ternaryClockR_cube (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ternaryClockR ω ^ 3 = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hω3 : ω ^ 3 = 1 := omega_cube_eq_one ω hω
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [pow_succ, pow_zero, ternaryClockR, Matrix.mul_apply, Fin.sum_univ_three];
     try ring_nf; try simp [hω3])
  · calc
      ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3]; ring

/-- **Weyl–Sylvester–Morris–Shirokov $\omega$-Commutation Law** (Eq. 2.51 / 3.48 of `arXiv:2504.19689`):
For $\omega^2 + \omega + 1 = 0$, the shift and clock generators $P = \beta(e_1)$ and
$R(\omega) = \beta(e_2)$ satisfy $P R(\omega) = \omega R(\omega) P$. -/
theorem ternaryShiftP_mul_ternaryClockR_comm (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    ternaryShiftP * ternaryClockR ω = ω • (ternaryClockR ω * ternaryShiftP) := by
  have hω3 : ω ^ 3 = 1 := omega_cube_eq_one ω hω
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [ternaryShiftP, ternaryClockR, Matrix.mul_apply, Fin.sum_univ_three];
     try ring_nf; try exact hω3.symm)

/-- General 9-component ternary Clifford multivector
$U = u_{00} I_3 + u_{10} P + u_{01} R + u_{20} P^2 + u_{02} R^2 + u_{11} P R + u_{21} P^2 R + u_{12} P R^2 + u_{22} P^2 R^2$
in $C\ell_2^{\frac{1}{3}} \cong M_3(\mathbb{C})$ (Eq. 2.59 / 3.102 of `arXiv:2504.19689`). -/
def ternaryMultivector (ω u00 u10 u01 u20 u02 u11 u21 u12 u22 : ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  u00 • (1 : Matrix (Fin 3) (Fin 3) ℂ) +
    u10 • ternaryShiftP +
    u01 • ternaryClockR ω +
    u20 • (ternaryShiftP ^ 2) +
    u02 • (ternaryClockR ω ^ 2) +
    u11 • (ternaryShiftP * ternaryClockR ω) +
    u21 • (ternaryShiftP ^ 2 * ternaryClockR ω) +
    u12 • (ternaryShiftP * ternaryClockR ω ^ 2) +
    u22 • (ternaryShiftP ^ 2 * ternaryClockR ω ^ 2)

/-!
## Section 2: Basis-Free Grade-0 Projection $\langle U \rangle_0 = \frac{1}{3}\operatorname{tr}(U)$ and Unitary Hermitian Conjugation
-/

/-- Shirokov's normalized grade-0 projection $\langle U \rangle_0 = \frac{1}{3}\operatorname{tr}(U)$
for the ternary Clifford algebra $C\ell_2^{\frac{1}{3}} \cong M_3(\mathbb{C})$
($N = 3^{2/2} = 3$, Lemma 7.1 of `arXiv:2504.19689`). -/
def ternaryShirokovGrade0 (U : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  (1 / 3 : ℂ) * Matrix.trace U

/-- The grade-0 projection of the identity matrix $I_3$ equals $1$. -/
theorem ternaryShirokovGrade0_one :
    ternaryShirokovGrade0 (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
  unfold ternaryShirokovGrade0
  simp [Matrix.trace, Matrix.diag]

/-- **Cyclic Symmetry of Shirokov's Ternary Grade-0 Projection** (Corollary 7.2 of `arXiv:2504.19689`):
$\langle U V \rangle_0 = \langle V U \rangle_0$ for all $U, V \in M_3(\mathbb{C})$. -/
theorem ternaryShirokovGrade0_mul_comm (U V : Matrix (Fin 3) (Fin 3) ℂ) :
    ternaryShirokovGrade0 (U * V) = ternaryShirokovGrade0 (V * U) := by
  unfold ternaryShirokovGrade0
  rw [Matrix.trace_mul_comm U V]

/-- **Lemma 7.1 of `arXiv:2504.19689`**: For $\omega^2 + \omega + 1 = 0$, the matrix trace of
any 9-component ternary multivector $U \in C\ell_2^{\frac{1}{3}}$ equals $3 u_{00}$, because
all 8 non-scalar basis monomials $e_1^j e_2^k$ ($(j, k) \neq (0, 0)$) are traceless
(since $1 + \omega + \omega^2 = 0$). -/
theorem ternaryMultivector_trace_eq
    (ω u00 u10 u01 u20 u02 u11 u21 u12 u22 : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Matrix.trace (ternaryMultivector ω u00 u10 u01 u20 u02 u11 u21 u12 u22) = 3 * u00 := by
  have _ := (u10, u20, u11, u21, u12, u22)
  unfold ternaryMultivector ternaryShiftP ternaryClockR
  simp [pow_succ, pow_zero, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  linear_combination (u01 + u02 * (ω ^ 2 - ω + 1)) * hω

/-- Shirokov's normalized grade-0 projection $\langle U \rangle_0 = \frac{1}{3}\operatorname{tr}(U)$
extracts the exact scalar coefficient $u_{00}$ of any 9-component ternary Clifford multivector. -/
theorem ternaryShirokovGrade0_multivector
    (ω u00 u10 u01 u20 u02 u11 u21 u12 u22 : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    ternaryShirokovGrade0 (ternaryMultivector ω u00 u10 u01 u20 u02 u11 u21 u12 u22) = u00 := by
  unfold ternaryShirokovGrade0
  rw [ternaryMultivector_trace_eq ω u00 u10 u01 u20 u02 u11 u21 u12 u22 hω]
  linear_combination

/-- **Theorem 5.1 (Shift Generator Unitarity)**: The Hermitian transpose of $P = \beta(e_1)$
equals its inverse $P^2 = \beta(e_1^{-1})$, so $P^{\mathrm{H}} P = I_3$. -/
theorem ternaryShiftP_conjTranspose_eq_sq :
    ternaryShiftPᴴ = ternaryShiftP ^ 2 ∧
    ternaryShiftPᴴ * ternaryShiftP = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, pow_zero, ternaryShiftP, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ternaryShiftP, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_three]

/-- **Theorem 5.1 (Clock Generator Unitarity)**: When $\omega^2 + \omega + 1 = 0$ and
$\bar{\omega} = \omega^2$, the Hermitian transpose of $R(\omega) = \beta(e_2)$ equals its
inverse $R(\omega)^2 = \beta(e_2^{-1})$, so $R(\omega)^{\mathrm{H}} R(\omega) = I_3$. -/
theorem ternaryClockR_conjTranspose_eq_sq (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) (hconj : star ω = ω ^ 2) :
    (ternaryClockR ω)ᴴ = ternaryClockR ω ^ 2 ∧
    (ternaryClockR ω)ᴴ * ternaryClockR ω = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hconj_end : (starRingEnd ℂ) ω = ω ^ 2 := hconj
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, pow_zero, ternaryClockR, Matrix.conjTranspose_apply,
        Matrix.mul_apply, Fin.sum_univ_three, hconj_end]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ternaryClockR, Matrix.conjTranspose_apply, Matrix.mul_apply,
        Fin.sum_univ_three, hconj_end]
    · linear_combination (ω - 1) * hω
    · linear_combination (ω ^ 3 + 1) * (ω - 1) * hω

/-!
## Section 3: Shirokov's Flattening Operator $\underline{U}$, Characteristic Polynomial Coefficients, Adjugate, and Matrix-Free Inverse in $C\ell_2^{\frac{1}{3}}$
-/

/-- Shirokov's involution-like sign-reversal operator on higher grades
$\underline{U} := \langle U \rangle_0 I_3 - \sum_{k \ge 1} \langle U \rangle_k = 2 \langle U \rangle_0 I_3 - U$
(Eq. 7.61 of `arXiv:2504.19689`). -/
def ternaryUnderline (U : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (2 * ternaryShirokovGrade0 U) • (1 : Matrix (Fin 3) (Fin 3) ℂ) - U

/-- **Equation 7.67 of `arXiv:2504.19689`**: $U + \underline{U} = 2 \langle U \rangle_0 I_3$. -/
theorem add_ternaryUnderline_eq_two_grade0 (U : Matrix (Fin 3) (Fin 3) ℂ) :
    U + ternaryUnderline U = (2 * ternaryShirokovGrade0 U) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  unfold ternaryUnderline
  abel

/-- The grade-0 projection of $\underline{U}$ equals $\langle U \rangle_0$. -/
theorem ternaryShirokovGrade0_ternaryUnderline (U : Matrix (Fin 3) (Fin 3) ℂ) :
    ternaryShirokovGrade0 (ternaryUnderline U) = ternaryShirokovGrade0 U := by
  unfold ternaryUnderline ternaryShirokovGrade0
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  linear_combination

/-- **Theorem 7.7(1) of `arXiv:2504.19689`** (Eq. 7.73): $\underline{U}$ is an involution
($\underline{\underline{U}} = U$), additive ($\underline{U + V} = \underline{U} + \underline{V}$),
and $\mathbb{C}$-linear ($\underline{\alpha U} = \alpha \underline{U}$). -/
theorem ternaryUnderline_involutive_and_linear
    (α : ℂ) (U V : Matrix (Fin 3) (Fin 3) ℂ) :
    ternaryUnderline (ternaryUnderline U) = U ∧
    ternaryUnderline (U + V) = ternaryUnderline U + ternaryUnderline V ∧
    ternaryUnderline (α • U) = α • ternaryUnderline U := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp [ternaryUnderline, ternaryShirokovGrade0, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    ring
  · ext i j
    simp [ternaryUnderline, ternaryShirokovGrade0, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    ring
  · ext i j
    simp [ternaryUnderline, ternaryShirokovGrade0, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    ring

/-- **Theorem 7.7(2) of `arXiv:2504.19689`** (Eq. 7.74): Shift identity
$\underline{U V} U = U \underline{V U}$ for all $U, V \in M_3(\mathbb{C})$. -/
theorem ternaryUnderline_mul_shift (U V : Matrix (Fin 3) (Fin 3) ℂ) :
    ternaryUnderline (U * V) * U = U * ternaryUnderline (V * U) := by
  unfold ternaryUnderline
  rw [ternaryShirokovGrade0_mul_comm U V, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, mul_assoc]

/-- **Theorem 7.7(3) of `arXiv:2504.19689`** (Eq. 7.75): Nested flattening identity
$\underline{U \underline{V}} = \underline{U}\,\underline{V} + \underline{U} V - \underline{U V}$. -/
theorem ternaryUnderline_nested (U V : Matrix (Fin 3) (Fin 3) ℂ) :
    ternaryUnderline (U * ternaryUnderline V) =
      ternaryUnderline U * ternaryUnderline V + ternaryUnderline U * V -
        ternaryUnderline (U * V) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [ternaryUnderline, ternaryShirokovGrade0, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_three];
     ring)

/-- **Equation 7.92 of `arXiv:2504.19689`**: Self-nested flattening identity
$\underline{U \underline{U}} = (\underline{U})^2 + \underline{U} U - \underline{U^2}$. -/
theorem ternaryUnderline_self_nested (U : Matrix (Fin 3) (Fin 3) ℂ) :
    ternaryUnderline (U * ternaryUnderline U) =
      (ternaryUnderline U) ^ 2 + ternaryUnderline U * U - ternaryUnderline (U ^ 2) := by
  rw [sq, sq, ternaryUnderline_nested U U]

/-- First characteristic polynomial coefficient $C_{(1)}(U) = 3 \langle U \rangle_0 = \operatorname{tr}(U)$
in $C\ell_2^{\frac{1}{3}}$ (Eq. 8.10 of `arXiv:2504.19689`). -/
def ternaryCharC1 (U : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  3 * ternaryShirokovGrade0 U

/-- Second characteristic polynomial coefficient
$C_{(2)}(U) = \frac{1}{2}(\operatorname{tr}(U^2) - \operatorname{tr}(U)^2)$ in Shirokov's convention
$\varphi_U(\lambda) = \lambda^3 - C_{(1)}\lambda^2 - C_{(2)}\lambda - C_{(3)}$
(Eqs. 8.06 & 8.11 of `arXiv:2504.19689`). -/
def ternaryCharC2 (U : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  (1 / 2 : ℂ) * (Matrix.trace (U ^ 2) - (Matrix.trace U) ^ 2)

/-- **Equation 8.11 of `arXiv:2504.19689`**: Shirokov's basis-free formula for $C_{(2)}(U) I_3$:
$-\frac{3}{8}(U^2 + \underline{U^2} + 3 U \underline{U} + 3 \underline{U \underline{U}}) = C_{(2)}(U) I_3$. -/
theorem ternaryCharC2_shirokov_formula (U : Matrix (Fin 3) (Fin 3) ℂ) :
    (-(3 / 8 : ℂ)) •
        (U ^ 2 + ternaryUnderline (U ^ 2) +
          (3 : ℂ) • (U * ternaryUnderline U) +
          (3 : ℂ) • ternaryUnderline (U * ternaryUnderline U)) =
      ternaryCharC2 U • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [ternaryCharC2, ternaryUnderline, ternaryShirokovGrade0, pow_two,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three];
     ring)

/-- Shirokov's basis-free adjugate in $C\ell_2^{\frac{1}{3}}$ (Eq. 8.25 of `arXiv:2504.19689`):
$\operatorname{Adj}(U) = \frac{1}{8}(-U^2 - 3 U \underline{U} + 3 \underline{U^2} + 9 \underline{U \underline{U}})$. -/
def ternaryShirokovAdjugate (U : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 8 : ℂ) •
    (-U ^ 2 - (3 : ℂ) • (U * ternaryUnderline U) +
      (3 : ℂ) • ternaryUnderline (U ^ 2) +
      (9 : ℂ) • ternaryUnderline (U * ternaryUnderline U))

/-- **Equations 8.36 & 7.53 of `arXiv:2504.19689`**: Equivalent flattened form of
$\operatorname{Adj}(U)$ and its Faddeev–LeVerrier identity
$\operatorname{Adj}(U) = U^2 - C_{(1)}(U) U - C_{(2)}(U) I_3$. -/
theorem ternaryShirokovAdjugate_flattened_and_faddeevLeVerrier
    (U : Matrix (Fin 3) (Fin 3) ℂ) :
    ternaryShirokovAdjugate U =
      (1 / 8 : ℂ) •
        (-U ^ 2 - (6 : ℂ) • ternaryUnderline (U ^ 2) +
          (6 : ℂ) • (U * ternaryUnderline U) +
          (9 : ℂ) • (ternaryUnderline U) ^ 2) ∧
    ternaryShirokovAdjugate U =
      U ^ 2 - ternaryCharC1 U • U - ternaryCharC2 U • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [ternaryShirokovAdjugate, ternaryUnderline, ternaryShirokovGrade0, pow_two,
        Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three];
       ring)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [ternaryShirokovAdjugate, ternaryCharC1, ternaryCharC2, ternaryUnderline,
        ternaryShirokovGrade0, pow_two, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fin.sum_univ_three];
       ring)

/-- **Shirokov's Basis-Free Cubic Determinant & Cayley–Hamilton Identity in $C\ell_2^{\frac{1}{3}}$**
(Eqs. 8.12, 8.25, & 8.29 of `arXiv:2504.19689`):
For every $U \in M_3(\mathbb{C})$, the product of $U$ with its basis-free Shirokov adjugate
$\operatorname{Adj}(U) = \frac{1}{8}(-U^2 - 3 U \underline{U} + 3 \underline{U^2} + 9 \underline{U \underline{U}})$
is the exact scalar multiple $\det(U) I_3$ on both sides:
$U \cdot \operatorname{Adj}(U) = \det(U) I_3 = \operatorname{Adj}(U) \cdot U$. -/
theorem ternaryShirokov_adjugate_mul_eq_det (U : Matrix (Fin 3) (Fin 3) ℂ) :
    U * ternaryShirokovAdjugate U = Matrix.det U • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
    ternaryShirokovAdjugate U * U = Matrix.det U • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (rw [Matrix.det_fin_three];
       simp [ternaryShirokovAdjugate, ternaryUnderline, ternaryShirokovGrade0, pow_two,
         Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three];
       ring)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (rw [Matrix.det_fin_three];
       simp [ternaryShirokovAdjugate, ternaryUnderline, ternaryShirokovGrade0, pow_two,
         Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three];
       ring)

/-- **Equation 8.16 of `arXiv:2504.19689`**: The ternary Clifford generators $I_3$, $P = \beta(e_1)$,
and $R(\omega) = \beta(e_2)$ (for $\omega^2 + \omega + 1 = 0$) all have unit determinant
$\operatorname{Det}(e) = \operatorname{Det}(e_1) = \operatorname{Det}(e_2) = 1$, placing them in
$\mathrm{SU}C\ell_2^{\frac{1}{3}} \cong \mathrm{SU}(3)$. -/
theorem ternaryShirokov_generators_det_one (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Matrix.det (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 ∧
    Matrix.det ternaryShiftP = 1 ∧
    Matrix.det (ternaryClockR ω) = 1 := by
  have hω3 : ω ^ 3 = 1 := omega_cube_eq_one ω hω
  refine ⟨Matrix.det_one, ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    simp [ternaryShiftP]
  · rw [Matrix.det_fin_three]
    simp [ternaryClockR]
    calc
      ω * ω ^ 2 = ω ^ 3 := by ring
      _ = 1 := hω3

/-- **Corollary 7.6 & Equation 8.21 of `arXiv:2504.19689` (Basis-Free Inverse in $C\ell_2^{\frac{1}{3}}$)**:
Whenever $\det(U) \cdot \mathrm{invDet} = 1$, the scaled Shirokov adjugate
$U^{-1} = \mathrm{invDet} \cdot \operatorname{Adj}(U)$ is the exact two-sided multiplicative
inverse of $U$ in $C\ell_2^{\frac{1}{3}} \cong M_3(\mathbb{C})$. -/
theorem ternaryShirokov_inverse_formula
    (U : Matrix (Fin 3) (Fin 3) ℂ) (invDet : ℂ)
    (h_inv : Matrix.det U * invDet = 1) :
    U * (invDet • ternaryShirokovAdjugate U) = (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
    (invDet • ternaryShirokovAdjugate U) * U = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have h_comm : invDet * Matrix.det U = 1 := by
    rw [mul_comm, h_inv]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mul_smul, (ternaryShirokov_adjugate_mul_eq_det U).1,
        smul_smul, h_comm, one_smul]
  · rw [Matrix.smul_mul, (ternaryShirokov_adjugate_mul_eq_det U).2,
        smul_smul, h_comm, one_smul]

/-!
## Section 4: Special Unitary Lie Algebra $\mathfrak{su}C\ell_2^{\frac{1}{3}} \cong \mathfrak{su}(3)$ (`ternarySU3LieElement_commutator`) and Transition to the 8 Gell-Mann Color Generators
-/

/-- Membership predicate for Shirokov's skew-Hermitian grade-0-traceless subspace
$\mathfrak{su}C\ell_2^{\frac{1}{3}} = \{ X \in M_3(\mathbb{C}) \mid X^{\mathrm{H}} = -X \land \langle X \rangle_0 = 0 \}$
(`ternarySU3LieElement_commutator`, Corollary 8.2 & Eq. 8.83 of `arXiv:2504.19689`). -/
def IsTernarySU3LieElement (X : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  Xᴴ = -X ∧ ternaryShirokovGrade0 X = 0

/-- **Corollary 8.2 of `arXiv:2504.19689`**: The skew-Hermitian grade-0-traceless subspace
$\mathfrak{su}C\ell_2^{\frac{1}{3}}$ is closed under the Lie commutator $\lbrack X, Y \rbrack = X Y - Y X$. -/
theorem ternarySU3LieElement_commutator
    (X Y : Matrix (Fin 3) (Fin 3) ℂ)
    (hX : IsTernarySU3LieElement X) (hY : IsTernarySU3LieElement Y) :
    IsTernarySU3LieElement (X * Y - Y * X) := by
  rcases hX with ⟨hXH, _⟩
  rcases hY with ⟨hYH, _⟩
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hXH, hYH]
    noncomm_ring
  · unfold ternaryShirokovGrade0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm X Y, sub_self, mul_zero]

/-- Shirokov's first ternary Clifford $\mathfrak{su}(3)$ generator
$\beta_1 = \beta(e_1 - e_1^2) = P - P^2$ (Eqs. 8.95 & 9.03 of `arXiv:2504.19689`). -/
def shirokovBeta1 : Matrix (Fin 3) (Fin 3) ℂ :=
  ternaryShiftP - ternaryShiftP ^ 2

/-- Shirokov's second ternary Clifford $\mathfrak{su}(3)$ generator
$\beta_2 = \beta(i(e_1 + e_1^2)) = i(P + P^2)$ (Eqs. 8.95 & 9.08 of `arXiv:2504.19689`). -/
def shirokovBeta2 : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • (ternaryShiftP + ternaryShiftP ^ 2)

/-- Shirokov's third ternary Clifford $\mathfrak{su}(3)$ generator
$\beta_3(\omega) = \beta(e_2 - e_2^2) = R(\omega) - R(\omega)^2$
(Eqs. 8.97 & 9.15 of `arXiv:2504.19689`). -/
def shirokovBeta3 (ω : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ternaryClockR ω - ternaryClockR ω ^ 2

/-- Shirokov's fourth ternary Clifford $\mathfrak{su}(3)$ generator
$\beta_4(\omega) = \beta(i(e_2 + e_2^2)) = i(R(\omega) + R(\omega)^2)$
(Eqs. 8.97 & 9.21 of `arXiv:2504.19689`). -/
def shirokovBeta4 (ω : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Complex.I • (ternaryClockR ω + ternaryClockR ω ^ 2)

/-- Anti-Hermitian Gell-Mann generator $\theta_1 = i \lambda_1$ (Eqs. 956 & 960). -/
def gellMannTheta1 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, Complex.I, 0;
     Complex.I, 0, 0;
     0, 0, 0]

/-- Anti-Hermitian Gell-Mann generator $\theta_2 = i \lambda_2$ (Eqs. 956 & 965). -/
def gellMannTheta2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 1, 0;
     -1, 0, 0;
     0, 0, 0]

/-- Anti-Hermitian Gell-Mann Cartan generator $\theta_3 = i \lambda_3$ (Eqs. 956 & 970). -/
def gellMannTheta3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.I, 0, 0;
     0, -Complex.I, 0;
     0, 0, 0]

/-- Anti-Hermitian Gell-Mann generator $\theta_4 = i \lambda_4$ (Eqs. 956 & 975). -/
def gellMannTheta4 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, Complex.I;
     0, 0, 0;
     Complex.I, 0, 0]

/-- Anti-Hermitian Gell-Mann generator $\theta_5 = i \lambda_5$ (Eqs. 956 & 980). -/
def gellMannTheta5 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 1;
     0, 0, 0;
     -1, 0, 0]

/-- Anti-Hermitian Gell-Mann generator $\theta_6 = i \lambda_6$ (Eqs. 956 & 985). -/
def gellMannTheta6 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     0, 0, Complex.I;
     0, Complex.I, 0]

/-- Anti-Hermitian Gell-Mann generator $\theta_7 = i \lambda_7$ (Eqs. 956 & 990). -/
def gellMannTheta7 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0;
     0, 0, 1;
     0, -1, 0]

/-- Scaled anti-Hermitian Gell-Mann hypercharge Cartan generator
$\sqrt{3}\,\theta_8 = i \sqrt{3}\,\lambda_8 = \operatorname{diag}(i, i, -2i)$
(Eqs. 956 & 995 of `arXiv:2504.19689`). -/
def gellMannSqrt3Theta8 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![Complex.I, 0, 0;
     0, Complex.I, 0;
     0, 0, -2 * Complex.I]

/-- Shirokov's shift-sector generators $\beta_1 = P - P^2$ and $\beta_2 = i(P + P^2)$ belong to
$\mathfrak{su}C\ell_2^{\frac{1}{3}}$ and decompose into the off-diagonal Gell-Mann generators as
$\beta_1 = \theta_2 - \theta_5 + \theta_7$ and $\beta_2 = \theta_1 + \theta_4 + \theta_6$
(Eq. 1009 of `arXiv:2504.19689`). -/
theorem shirokovBeta1_beta2_su3_and_gellMann_decomp :
    IsTernarySU3LieElement shirokovBeta1 ∧
    IsTernarySU3LieElement shirokovBeta2 ∧
    shirokovBeta1 = gellMannTheta2 - gellMannTheta5 + gellMannTheta7 ∧
    shirokovBeta2 = gellMannTheta1 + gellMannTheta4 + gellMannTheta6 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shirokovBeta1, pow_succ, pow_zero, ternaryShiftP,
        Matrix.conjTranspose_apply]
  · unfold shirokovBeta1 ternaryShirokovGrade0
    simp [pow_succ, pow_zero, ternaryShiftP, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shirokovBeta2, pow_succ, pow_zero, ternaryShiftP,
        Matrix.conjTranspose_apply]
  · unfold shirokovBeta2 ternaryShirokovGrade0
    simp [pow_succ, pow_zero, ternaryShiftP, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shirokovBeta1, gellMannTheta2, gellMannTheta5, gellMannTheta7,
        pow_succ, pow_zero, ternaryShiftP]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shirokovBeta2, gellMannTheta1, gellMannTheta4, gellMannTheta6,
        pow_succ, pow_zero, ternaryShiftP]

/-- **Equations 915, 921, & 1010 of `arXiv:2504.19689` (Cartan Subalgebra Transition)**:
When $\omega^2 + \omega + 1 = 0$ and $\omega - \omega^2 = i s_3$ (with $s_3 = \sqrt{3}$),
Shirokov's clock-sector generators $\beta_3(\omega) = R(\omega) - R(\omega)^2$ and
$\beta_4(\omega) = i(R(\omega) + R(\omega)^2)$ are grade-0-traceless and related to the
Gell-Mann Cartan generators $\theta_3 = i \lambda_3$ and $\sqrt{3}\theta_8 = i\sqrt{3}\lambda_8$ by:
- $\beta_3(\omega) = \operatorname{diag}(0, i s_3, -i s_3) = -\frac{s_3}{2}\theta_3 + \frac{s_3}{2}(\sqrt{3}\theta_8)$,
- $\beta_4(\omega) = \operatorname{diag}(2i, -i, -i) = \frac{3}{2}\theta_3 + \frac{1}{2}(\sqrt{3}\theta_8)$,
with exact inverse reconstruction $\theta_3 = -\frac{1}{2 s_3}\beta_3(\omega) + \frac{1}{2}\beta_4(\omega)$
(Eq. 1019) and $\sqrt{3}\theta_8 = \frac{3}{2 s_3}\beta_3(\omega) + \frac{1}{2}\beta_4(\omega)$ (Eq. 1024). -/
theorem shirokovBeta3_beta4_cartan_gellMann_bridge
    (ω s3 invS3 : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0)
    (hs3 : ω - ω ^ 2 = Complex.I * s3)
    (h_invS3 : s3 * invS3 = 1) :
    ternaryShirokovGrade0 (shirokovBeta3 ω) = 0 ∧
    ternaryShirokovGrade0 (shirokovBeta4 ω) = 0 ∧
    shirokovBeta3 ω =
      (-(s3 / 2 : ℂ)) • gellMannTheta3 + (s3 / 2 : ℂ) • gellMannSqrt3Theta8 ∧
    shirokovBeta4 ω =
      ((3 / 2 : ℂ)) • gellMannTheta3 + (1 / 2 : ℂ) • gellMannSqrt3Theta8 ∧
    (-(invS3 / 2 : ℂ)) • shirokovBeta3 ω + (1 / 2 : ℂ) • shirokovBeta4 ω =
      gellMannTheta3 ∧
    (3 * invS3 / 2 : ℂ) • shirokovBeta3 ω + (1 / 2 : ℂ) • shirokovBeta4 ω =
      gellMannSqrt3Theta8 := by
  have hω3 : ω ^ 3 = 1 := omega_cube_eq_one ω hω
  have hω4 : ω ^ 4 = ω := by
    calc
      ω ^ 4 = ω * ω ^ 3 := by ring
      _ = ω := by rw [hω3]; ring
  have hωsq : ω * ω = ω ^ 2 := by ring
  have hsum : ω + ω ^ 2 = -1 := by linear_combination hω
  have hsumMul : ω + ω * ω = -1 := by rw [hωsq]; exact hsum
  have hsumPow2 : ω ^ 2 + ω ^ 4 = -1 := by rw [hω4]; linear_combination hsum
  have h_b3 :
      shirokovBeta3 ω =
        (-(s3 / 2 : ℂ)) • gellMannTheta3 + (s3 / 2 : ℂ) • gellMannSqrt3Theta8 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shirokovBeta3, gellMannTheta3, gellMannSqrt3Theta8,
        pow_succ, pow_zero, ternaryClockR]
    all_goals
      first
      | calc
          ω - ω * ω = ω - ω ^ 2 := by rw [hωsq]
          _ = Complex.I * s3 := hs3
          _ = s3 / 2 * Complex.I + s3 / 2 * Complex.I := by ring
      | calc
          ω * ω - ω * ω * (ω * ω) = ω ^ 2 - ω ^ 4 := by rw [hωsq]; ring
          _ = -(s3 * Complex.I) := by rw [hω4]; linear_combination -hs3
          _ = -(s3 / 2 * (2 * Complex.I)) := by ring
  have h_b4 :
      shirokovBeta4 ω =
        ((3 / 2 : ℂ)) • gellMannTheta3 + (1 / 2 : ℂ) • gellMannSqrt3Theta8 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shirokovBeta4, gellMannTheta3, gellMannSqrt3Theta8,
        pow_succ, pow_zero, ternaryClockR]
    all_goals
      first
      | calc
          Complex.I * (1 + 1) = 3 / 2 * Complex.I + 2⁻¹ * Complex.I := by ring
      | calc
          Complex.I * (ω + ω * ω) = Complex.I * (-1) := by rw [hsumMul]
          _ = -(3 / 2 * Complex.I) + 2⁻¹ * Complex.I := by ring
      | calc
          Complex.I * (ω * ω + ω * ω * (ω * ω)) = Complex.I * (-1) := by
            rw [hωsq]
            calc
              Complex.I * (ω ^ 2 + ω ^ 2 * ω ^ 2) =
                  Complex.I * (ω ^ 2 + ω ^ 4) := by congr 1; ring
              _ = Complex.I * (-1) := by rw [hsumPow2]
          _ = -Complex.I := by ring
  refine ⟨?_, ?_, h_b3, h_b4, ?_, ?_⟩
  · rw [h_b3]
    unfold ternaryShirokovGrade0
    simp [gellMannTheta3, gellMannSqrt3Theta8, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    ring
  · rw [h_b4]
    unfold ternaryShirokovGrade0
    simp [gellMannTheta3, gellMannSqrt3Theta8, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    ring
  · rw [h_b3, h_b4]
    have h_inv : invS3 * s3 = 1 := by rw [mul_comm]; exact h_invS3
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gellMannTheta3, gellMannSqrt3Theta8]
    all_goals (ring_nf; try rw [h_inv]; ring)
  · rw [h_b3, h_b4]
    have h_inv : invS3 * s3 = 1 := by rw [mul_comm]; exact h_invS3
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gellMannTheta3, gellMannSqrt3Theta8]
    all_goals (ring_nf; try rw [h_inv]; ring)

/-!
## Section 5: Master Quadratic-to-Ternary Shirokov & Color $\mathfrak{su}(3) / \mathfrak{sl}(3)$ Synthesis
-/

/-- **Master Quadratic-to-Ternary Shirokov & Color $\mathfrak{su}(3) / \mathfrak{sl}(3)$ Synthesis**:
Unites inside a single kernel-verified theorem:
1. Shirokov's quadratic ($m = 2$) matrix-free determinant identity in $\mathrm{Cl}(1,1) \cong M_2(\mathbb{R})$
   (`cl11_shirokov_det_formula`),
2. The ternary ($m = 3$) Clifford algebra $C\ell_2^{\frac{1}{3}} \cong M_3(\mathbb{C})$ relations
   $P^3 = I_3$, $R(\omega)^3 = I_3$, $P R(\omega) = \omega R(\omega) P$, and grade-0 scalar
   extraction $\langle U \rangle_0 = u_{00}$,
3. Shirokov's Theorem 7.7 flattening identity $\underline{U \underline{V}} = \underline{U}\,\underline{V} + \underline{U} V - \underline{U V}$
   and basis-free cubic determinant/adjugate/inverse theorem
   $U \cdot \operatorname{Adj}(U) = \det(U) I_3$ in $C\ell_2^{\frac{1}{3}}$,
4. The $\mathfrak{su}C\ell_2^{\frac{1}{3}} \cong \mathfrak{su}(3)$ Gell-Mann color decomposition
   $\beta_1 = \theta_2 - \theta_5 + \theta_7$ and $\beta_2 = \theta_1 + \theta_4 + \theta_6$, and
5. The real Peirce $\mathfrak{sl}_3(\mathbb{R})$ color intertwining on `ZornSplitOctonion ℝ`
   (`peirceAlignedZornGGEquiv_intertwines_realColor`). -/
theorem shirokov_ternary_clifford_unitary_su3_grand_synthesis
    (u0 u1 u2 u12 : ℝ)
    (ω u00 u10 u01 u20 u02 u11 u21 u12_c u22 : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0)
    (U V : Matrix (Fin 3) (Fin 3) ℂ)
    (L : Matrix (Fin 3) (Fin 3) ℝ) (hL : Matrix.trace L = 0)
    (z : InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge.ZornSplitOctonion ℝ) :
    (cl11Multivector u0 u1 u2 u12 * cl11CliffordConj u0 u1 u2 u12 =
      cl11DetScalar u0 u1 u2 u12 • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (ternaryShiftP ^ 3 = (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
     ternaryClockR ω ^ 3 = (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
     ternaryShiftP * ternaryClockR ω = ω • (ternaryClockR ω * ternaryShiftP)) ∧
    (ternaryShirokovGrade0 (ternaryMultivector ω u00 u10 u01 u20 u02 u11 u21 u12_c u22) = u00) ∧
    (ternaryUnderline (U * ternaryUnderline V) =
      ternaryUnderline U * ternaryUnderline V + ternaryUnderline U * V -
        ternaryUnderline (U * V) ∧
     U * ternaryShirokovAdjugate U = Matrix.det U • (1 : Matrix (Fin 3) (Fin 3) ℂ)) ∧
    (shirokovBeta1 = gellMannTheta2 - gellMannTheta5 + gellMannTheta7 ∧
     shirokovBeta2 = gellMannTheta1 + gellMannTheta4 + gellMannTheta6) ∧
    (peirceAlignedZornToGG
        (InfoGeometry.Synthesis.G2SplitSedenionDerivationBridge.zornG2Derivation
          (realColorParameters L hL) z) =
      evenColorTransform L (peirceAlignedZornToGG z)) :=
  ⟨(cl11_shirokov_det_formula u0 u1 u2 u12).1,
   ⟨ternaryShiftP_cube,
    ternaryClockR_cube ω hω,
    ternaryShiftP_mul_ternaryClockR_comm ω hω⟩,
   ternaryShirokovGrade0_multivector ω u00 u10 u01 u20 u02 u11 u21 u12_c u22 hω,
   ⟨ternaryUnderline_nested U V,
    (ternaryShirokov_adjugate_mul_eq_det U).1⟩,
   ⟨shirokovBeta1_beta2_su3_and_gellMann_decomp.2.2.1,
    shirokovBeta1_beta2_su3_and_gellMann_decomp.2.2.2⟩,
   peirceAlignedZornGGEquiv_intertwines_realColor L hL z⟩

end InfoGeometry.Synthesis.ShirokovTernaryCliffordUnitarySU3Synthesis
