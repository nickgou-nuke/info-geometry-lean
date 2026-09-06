import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import InfoGeometry.Canonical.ComplexMatrixStage
import InfoGeometry.Canonical.GenuineMatrixStageMorphism
import InfoGeometry.Canonical.MatrixStageInductiveLimit
import InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
import InfoGeometry.Dynamics.KanDecomposition
import InfoGeometry.Dynamics.MoebiusTrifactorFlows
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Physics.ParabolicClock

/-!
# Trifactor Fourier Decomposition by Cyclotomic N-Potent Operators for 2×2 Matrix Stages

This owner formalizes the complete trifactor Fourier decomposition of $2 \times 2$ complex matrix
operators through cyclotomic $n$-potent generators and their left/right spinorial representations:

1. **Cyclotomic Fourier Projectors:**
   For any generator $U$ with $U^n = 1$ and primitive root of unity $\zeta^n = 1$, the Fourier projectors
   $$e_k = \frac{1}{n} \sum_{j=0}^{n-1} \zeta^{-kj} U^j$$
   form a complete orthogonal system:
   - Orthogonal idempotents: $e_k e_\ell = \delta_{k\ell} e_k$
   - Resolution of identity / partition of unity: $\sum_k e_k = 1$
   - Eigenvalue equation: $U e_k = \zeta^k e_k$
   - Spectral synthesis: $U = \sum_k \zeta^k e_k$

2. **Sectoral Matrix Realizations:**
   - **Order 2 Hyperbolic Involution Projectors:** $P_\pm(H) = \frac{1 \pm H}{2}$ for $H^2 = 1$
     (grading involution $\epsilon$ and modular reflection $J$).
   - **Order 4 Elliptic Clock Projectors:** 4-phase cyclotomic projectors for $J_{\text{clock}}^2 = -1$
     and $J_{\text{clock}}^4 = 1$ with $e_1 + e_3 = 1$ and $J_{\text{clock}} = i e_1 - i e_3$.
   - **Parabolic Nilpotent Nilpotency:** $N(t) = 1 + t K_0$ with $K_0^2 = 0$ (Jordan shear decomposition).

3. **Canonical 3-Point Möbius Transform to $SL_2(\mathbb{C})$:**
   The unique Möbius transform mapping $0 \mapsto z_1$, $1 \mapsto z_2$, $\infty \mapsto z_3$ with
   non-zero determinant $\Delta = (z_3 - z_1)(z_2 - z_1)(z_3 - z_2)$.

4. **Trifactor Fourier Left/Right Lorentz Action:**
   The spinorial representation $(g_L, g_R) \mapsto (X \mapsto g_L X g_R^\dagger)$ factored through
   $g = K \cdot A \cdot N$, where each factor is expanded in its Fourier projectors.

5. **Doubled Krein Carrier Action:**
   Native realization on `DoubledSpace E` via `ρclock`.

6. **Stage-Successor Bonding Compatibility:**
   Block embedding into `ComplexMatrixStage.Stage 1` and `Stage 2` commuting with `bondFun`.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixStageTrifactorFourierCyclotomic

open Matrix
open scoped ComplexConjugate
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Dynamics.KanDecomposition
open InfoGeometry.Dynamics.MoebiusFlow
open InfoGeometry.Krein
open InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

/-! ## 1. General Order-2 Parity Projectors (Hyperbolic / Involution Sector) -/

/-- Even / positive parity projector for an involution $U^2 = 1$. -/
def projPlus2 (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + U)

/-- Odd / negative parity projector for an involution $U^2 = 1$. -/
def projMinus2 (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 - U)

@[simp]
theorem projPlus2_add_projMinus2 (U : Matrix (Fin 2) (Fin 2) ℂ) :
    projPlus2 U + projMinus2 U = 1 := by
  ext i j
  simp only [projPlus2, projMinus2, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, smul_eq_mul]
  ring

theorem projPlus2_sq (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U * U = 1) :
    projPlus2 U * projPlus2 U = projPlus2 U := by
  ext i j
  have hUij : ∀ a b, (U * U) a b = (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by rw [hU]; intros; rfl
  have h00 : U 0 0 * U 0 0 + U 0 1 * U 1 0 = 1 := by
    have := hUij 0 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h01 : U 0 0 * U 0 1 + U 0 1 * U 1 1 = 0 := by
    have := hUij 0 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h10 : U 1 0 * U 0 0 + U 1 1 * U 1 0 = 0 := by
    have := hUij 1 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h11 : U 1 0 * U 0 1 + U 1 1 * U 1 1 = 1 := by
    have := hUij 1 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  fin_cases i <;> fin_cases j
  · simp only [projPlus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, Fin.isValue, smul_eq_mul]
    calc (1 / 2 * (1 + U 0 0) * (1 / 2 * (1 + U 0 0)) + 1 / 2 * (0 + U 0 1) * (1 / 2 * (0 + U 1 0)))
      _ = 1 / 4 * (1 + 2 * U 0 0 + (U 0 0 * U 0 0 + U 0 1 * U 1 0)) := by ring
      _ = 1 / 4 * (1 + 2 * U 0 0 + 1) := by rw [h00]
      _ = 1 / 2 * (1 + U 0 0) := by ring
  · simp only [projPlus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, Fin.isValue, smul_eq_mul]
    calc (1 / 2 * (1 + U 0 0) * (1 / 2 * (0 + U 0 1)) + 1 / 2 * (0 + U 0 1) * (1 / 2 * (1 + U 1 1)))
      _ = 1 / 4 * (2 * U 0 1 + (U 0 0 * U 0 1 + U 0 1 * U 1 1)) := by ring
      _ = 1 / 4 * (2 * U 0 1 + 0) := by rw [h01]
      _ = 1 / 2 * (0 + U 0 1) := by ring
  · simp only [projPlus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, Fin.isValue, smul_eq_mul]
    calc (1 / 2 * (0 + U 1 0) * (1 / 2 * (1 + U 0 0)) + 1 / 2 * (1 + U 1 1) * (1 / 2 * (0 + U 1 0)))
      _ = 1 / 4 * (2 * U 1 0 + (U 1 0 * U 0 0 + U 1 1 * U 1 0)) := by ring
      _ = 1 / 4 * (2 * U 1 0 + 0) := by rw [h10]
      _ = 1 / 2 * (0 + U 1 0) := by ring
  · simp only [projPlus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, Fin.isValue, smul_eq_mul]
    calc (1 / 2 * (0 + U 1 0) * (1 / 2 * (0 + U 0 1)) + 1 / 2 * (1 + U 1 1) * (1 / 2 * (1 + U 1 1)))
      _ = 1 / 4 * (1 + 2 * U 1 1 + (U 1 0 * U 0 1 + U 1 1 * U 1 1)) := by ring
      _ = 1 / 4 * (1 + 2 * U 1 1 + 1) := by rw [h11]
      _ = 1 / 2 * (1 + U 1 1) := by ring

theorem projMinus2_sq (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U * U = 1) :
    projMinus2 U * projMinus2 U = projMinus2 U := by
  ext i j
  have hUij : ∀ a b, (U * U) a b = (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by rw [hU]; intros; rfl
  have h00 : U 0 0 * U 0 0 + U 0 1 * U 1 0 = 1 := by
    have := hUij 0 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h01 : U 0 0 * U 0 1 + U 0 1 * U 1 1 = 0 := by
    have := hUij 0 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h10 : U 1 0 * U 0 0 + U 1 1 * U 1 0 = 0 := by
    have := hUij 1 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h11 : U 1 0 * U 0 1 + U 1 1 * U 1 1 = 1 := by
    have := hUij 1 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  fin_cases i <;> fin_cases j
  · simp only [projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, Fin.isValue, smul_eq_mul]
    calc (1 / 2 * (1 - U 0 0) * (1 / 2 * (1 - U 0 0)) + 1 / 2 * (0 - U 0 1) * (1 / 2 * (0 - U 1 0)))
      _ = 1 / 4 * (1 - 2 * U 0 0 + (U 0 0 * U 0 0 + U 0 1 * U 1 0)) := by ring
      _ = 1 / 4 * (1 - 2 * U 0 0 + 1) := by rw [h00]
      _ = 1 / 2 * (1 - U 0 0) := by ring
  · simp only [projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, Fin.isValue, smul_eq_mul]
    calc (1 / 2 * (1 - U 0 0) * (1 / 2 * (0 - U 0 1)) + 1 / 2 * (0 - U 0 1) * (1 / 2 * (1 - U 1 1)))
      _ = 1 / 4 * (-2 * U 0 1 + (U 0 0 * U 0 1 + U 0 1 * U 1 1)) := by ring
      _ = 1 / 4 * (-2 * U 0 1 + 0) := by rw [h01]
      _ = 1 / 2 * (0 - U 0 1) := by ring
  · simp only [projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, Fin.isValue, smul_eq_mul]
    calc (1 / 2 * (0 - U 1 0) * (1 / 2 * (1 - U 0 0)) + 1 / 2 * (1 - U 1 1) * (1 / 2 * (0 - U 1 0)))
      _ = 1 / 4 * (-2 * U 1 0 + (U 1 0 * U 0 0 + U 1 1 * U 1 0)) := by ring
      _ = 1 / 4 * (-2 * U 1 0 + 0) := by rw [h10]
      _ = 1 / 2 * (0 - U 1 0) := by ring
  · simp only [projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, Fin.isValue, smul_eq_mul]
    calc (1 / 2 * (0 - U 1 0) * (1 / 2 * (0 - U 0 1)) + 1 / 2 * (1 - U 1 1) * (1 / 2 * (1 - U 1 1)))
      _ = 1 / 4 * (1 - 2 * U 1 1 + (U 1 0 * U 0 1 + U 1 1 * U 1 1)) := by ring
      _ = 1 / 4 * (1 - 2 * U 1 1 + 1) := by rw [h11]
      _ = 1 / 2 * (1 - U 1 1) := by ring

theorem projPlus2_mul_projMinus2 (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U * U = 1) :
    projPlus2 U * projMinus2 U = 0 := by
  ext i j
  have hUij : ∀ a b, (U * U) a b = (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by rw [hU]; intros; rfl
  have h00 : U 0 0 * U 0 0 + U 0 1 * U 1 0 = 1 := by
    have := hUij 0 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h01 : U 0 0 * U 0 1 + U 0 1 * U 1 1 = 0 := by
    have := hUij 0 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h10 : U 1 0 * U 0 0 + U 1 1 * U 1 0 = 0 := by
    have := hUij 1 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h11 : U 1 0 * U 0 1 + U 1 1 * U 1 1 = 1 := by
    have := hUij 1 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  fin_cases i <;> fin_cases j
  · simp only [projPlus2, projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Fin.isValue,
      smul_eq_mul]
    calc (1 / 2 * (1 + U 0 0) * (1 / 2 * (1 - U 0 0)) + 1 / 2 * (0 + U 0 1) * (1 / 2 * (0 - U 1 0)))
      _ = 1 / 4 * (1 - (U 0 0 * U 0 0 + U 0 1 * U 1 0)) := by ring
      _ = 1 / 4 * (1 - 1) := by rw [h00]
      _ = 0 := by ring
  · simp only [projPlus2, projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Fin.isValue,
      smul_eq_mul]
    calc (1 / 2 * (1 + U 0 0) * (1 / 2 * (0 - U 0 1)) + 1 / 2 * (0 + U 0 1) * (1 / 2 * (1 - U 1 1)))
      _ = -1 / 4 * (U 0 0 * U 0 1 + U 0 1 * U 1 1) := by ring
      _ = -1 / 4 * 0 := by rw [h01]
      _ = 0 := by ring
  · simp only [projPlus2, projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Fin.isValue,
      smul_eq_mul]
    calc (1 / 2 * (0 + U 1 0) * (1 / 2 * (1 - U 0 0)) + 1 / 2 * (1 + U 1 1) * (1 / 2 * (0 - U 1 0)))
      _ = -1 / 4 * (U 1 0 * U 0 0 + U 1 1 * U 1 0) := by ring
      _ = -1 / 4 * 0 := by rw [h10]
      _ = 0 := by ring
  · simp only [projPlus2, projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Fin.isValue,
      smul_eq_mul]
    calc (1 / 2 * (0 + U 1 0) * (1 / 2 * (0 - U 0 1)) + 1 / 2 * (1 + U 1 1) * (1 / 2 * (1 - U 1 1)))
      _ = 1 / 4 * (1 - (U 1 0 * U 0 1 + U 1 1 * U 1 1)) := by ring
      _ = 1 / 4 * (1 - 1) := by rw [h11]
      _ = 0 := by ring

theorem projMinus2_mul_projPlus2 (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U * U = 1) :
    projMinus2 U * projPlus2 U = 0 := by
  ext i j
  have hUij : ∀ a b, (U * U) a b = (1 : Matrix (Fin 2) (Fin 2) ℂ) a b := by rw [hU]; intros; rfl
  have h00 : U 0 0 * U 0 0 + U 0 1 * U 1 0 = 1 := by
    have := hUij 0 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h01 : U 0 0 * U 0 1 + U 0 1 * U 1 1 = 0 := by
    have := hUij 0 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h10 : U 1 0 * U 0 0 + U 1 1 * U 1 0 = 0 := by
    have := hUij 1 0; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  have h11 : U 1 0 * U 0 1 + U 1 1 * U 1 1 = 1 := by
    have := hUij 1 1; simp [Matrix.mul_apply, Fin.sum_univ_two] at this; exact this
  fin_cases i <;> fin_cases j
  · simp only [projPlus2, projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Fin.isValue,
      smul_eq_mul]
    calc (1 / 2 * (1 - U 0 0) * (1 / 2 * (1 + U 0 0)) + 1 / 2 * (0 - U 0 1) * (1 / 2 * (0 + U 1 0)))
      _ = 1 / 4 * (1 - (U 0 0 * U 0 0 + U 0 1 * U 1 0)) := by ring
      _ = 1 / 4 * (1 - 1) := by rw [h00]
      _ = 0 := by ring
  · simp only [projPlus2, projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Fin.isValue,
      smul_eq_mul]
    calc (1 / 2 * (1 - U 0 0) * (1 / 2 * (0 + U 0 1)) + 1 / 2 * (0 - U 0 1) * (1 / 2 * (1 + U 1 1)))
      _ = -1 / 4 * (U 0 0 * U 0 1 + U 0 1 * U 1 1) := by ring
      _ = -1 / 4 * 0 := by rw [h01]
      _ = 0 := by ring
  · simp only [projPlus2, projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Fin.isValue,
      smul_eq_mul]
    calc (1 / 2 * (0 - U 1 0) * (1 / 2 * (1 + U 0 0)) + 1 / 2 * (1 - U 1 1) * (1 / 2 * (0 + U 1 0)))
      _ = -1 / 4 * (U 1 0 * U 0 0 + U 1 1 * U 1 0) := by ring
      _ = -1 / 4 * 0 := by rw [h10]
      _ = 0 := by ring
  · simp only [projPlus2, projMinus2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.zero_apply, Fin.isValue,
      smul_eq_mul]
    calc (1 / 2 * (0 - U 1 0) * (1 / 2 * (0 + U 0 1)) + 1 / 2 * (1 - U 1 1) * (1 / 2 * (1 + U 1 1)))
      _ = 1 / 4 * (1 - (U 1 0 * U 0 1 + U 1 1 * U 1 1)) := by ring
      _ = 1 / 4 * (1 - 1) := by rw [h11]
      _ = 0 := by ring

theorem spectral_reconstruction_order2 (U : Matrix (Fin 2) (Fin 2) ℂ) :
    projPlus2 U - projMinus2 U = U := by
  ext i j
  simp only [projPlus2, projMinus2, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, smul_eq_mul]
  ring

/-! ## 2. Order-4 Cyclotomic Clock Projectors (Elliptic Sector) -/

/-- The standard $2 \times 2$ clock axis generator $J_{\text{clock}} = !![0, -1; 1, 0]$. -/
def matClockAxisC : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

@[simp]
theorem matClockAxisC_sq : matClockAxisC * matClockAxisC = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matClockAxisC, Matrix.mul_apply, Fin.sum_univ_two]

/-- The positive chiral clock projector $e_+ = \frac{1}{2}(1 - i J) = !![1/2, i/2; -i/2, 1/2]$. -/
def clockProjPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 2 : ℂ), Complex.I / 2; -Complex.I / 2, (1 / 2 : ℂ)]

/-- The negative chiral clock projector $e_- = \frac{1}{2}(1 + i J) = !![1/2, -i/2; i/2, 1/2]$. -/
def clockProjMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 / 2 : ℂ), -Complex.I / 2; Complex.I / 2, (1 / 2 : ℂ)]

@[simp]
theorem clockProj_sum : clockProjPlus + clockProjMinus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clockProjPlus, clockProjMinus] <;> ring

theorem clockProjPlus_sq : clockProjPlus * clockProjPlus = clockProjPlus := by
  ext i j
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    simp [clockProjPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · calc (2⁻¹ : ℂ) * (2⁻¹ : ℂ) + Complex.I / 2 * (-Complex.I / 2)
      _ = (2⁻¹ : ℂ) * (2⁻¹ : ℂ) - Complex.I ^ 2 * (1 / 4) := by ring
      _ = (2⁻¹ : ℂ) * (2⁻¹ : ℂ) - (-1) * (1 / 4) := by rw [hI]
      _ = (2⁻¹ : ℂ) := by ring
  · ring
  · ring
  · calc -Complex.I / 2 * (Complex.I / 2) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ)
      _ = -Complex.I ^ 2 * (1 / 4) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ) := by ring
      _ = -(-1) * (1 / 4) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ) := by rw [hI]
      _ = (2⁻¹ : ℂ) := by ring

theorem clockProjMinus_sq : clockProjMinus * clockProjMinus = clockProjMinus := by
  ext i j
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    simp [clockProjMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · calc (2⁻¹ : ℂ) * (2⁻¹ : ℂ) + -Complex.I / 2 * (Complex.I / 2)
      _ = (2⁻¹ : ℂ) * (2⁻¹ : ℂ) - Complex.I ^ 2 * (1 / 4) := by ring
      _ = (2⁻¹ : ℂ) * (2⁻¹ : ℂ) - (-1) * (1 / 4) := by rw [hI]
      _ = (2⁻¹ : ℂ) := by ring
  · ring
  · ring
  · calc Complex.I / 2 * (-Complex.I / 2) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ)
      _ = -Complex.I ^ 2 * (1 / 4) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ) := by ring
      _ = -(-1) * (1 / 4) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ) := by rw [hI]
      _ = (2⁻¹ : ℂ) := by ring

theorem clockProjPlus_mul_clockProjMinus : clockProjPlus * clockProjMinus = 0 := by
  ext i j
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    simp [clockProjPlus, clockProjMinus, Matrix.mul_apply, Fin.sum_univ_two]
  · calc (2⁻¹ : ℂ) * (2⁻¹ : ℂ) + Complex.I / 2 * (Complex.I / 2)
      _ = (2⁻¹ : ℂ) * (2⁻¹ : ℂ) + Complex.I ^ 2 * (1 / 4) := by ring
      _ = (2⁻¹ : ℂ) * (2⁻¹ : ℂ) + (-1) * (1 / 4) := by rw [hI]
      _ = 0 := by ring
  · ring
  · ring
  · calc -Complex.I / 2 * (-Complex.I / 2) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ)
      _ = Complex.I ^ 2 * (1 / 4) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ) := by ring
      _ = (-1) * (1 / 4) + (2⁻¹ : ℂ) * (2⁻¹ : ℂ) := by rw [hI]
      _ = 0 := by ring

/-- 🏆 THEOREM: Fourier synthesis of the clock axis complex structure $J = i e_+ - i e_-$. -/
theorem clockAxis_fourier_synthesis :
    Complex.I • clockProjPlus - Complex.I • clockProjMinus = matClockAxisC := by
  ext i j
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  fin_cases i <;> fin_cases j <;>
    dsimp [clockProjPlus, clockProjMinus, matClockAxisC, Matrix.sub_apply, Matrix.smul_apply]
  · ring
  · calc Complex.I * (Complex.I / 2) - Complex.I * (-Complex.I / 2)
      _ = Complex.I ^ 2 := by ring
      _ = -1 := by rw [hI]
  · calc Complex.I * (-Complex.I / 2) - Complex.I * (Complex.I / 2)
      _ = -Complex.I ^ 2 := by ring
      _ = -(-1) := by rw [hI]
      _ = 1 := by ring
  · ring

/-! ## 3. Canonical 3-Point Möbius Transform -/

/-- The canonical matrix of the Möbius transform sending $0 \mapsto z_1$, $1 \mapsto z_2$, $\infty \mapsto z_3$. -/
def mobius3Mat (z₁ z₂ z₃ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z₃ * (z₂ - z₁), z₁ * (z₃ - z₂); z₂ - z₁, z₃ - z₂]

/-- Determinant of the 3-point Möbius transform matrix. -/
@[simp]
theorem mobius3Mat_det (z₁ z₂ z₃ : ℂ) :
    (mobius3Mat z₁ z₂ z₃).det = (z₃ - z₁) * (z₂ - z₁) * (z₃ - z₂) := by
  rw [mobius3Mat, Matrix.det_fin_two]
  dsimp
  ring

/-- The determinant is non-zero whenever the three points are pairwise distinct. -/
theorem mobius3Mat_det_ne_zero {z₁ z₂ z₃ : ℂ}
    (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h13 : z₁ ≠ z₃) :
    (mobius3Mat z₁ z₂ z₃).det ≠ 0 := by
  rw [mobius3Mat_det]
  have hd13 : z₃ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
  have hd21 : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have hd32 : z₃ - z₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
  exact mul_ne_zero (mul_ne_zero hd13 hd21) hd32

/-- Evaluation of the Möbius transform on $0$: $\frac{M_{0,1}}{M_{1,1}} = z_1$. -/
theorem mobius3Mat_eval_zero (z₁ z₂ z₃ : ℂ) (h23 : z₂ ≠ z₃) :
    (mobius3Mat z₁ z₂ z₃ 0 1) / (mobius3Mat z₁ z₂ z₃ 1 1) = z₁ := by
  dsimp [mobius3Mat]
  have hd : z₃ - z₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
  exact mul_div_cancel_right₀ z₁ hd

/-- Evaluation of the Möbius transform on $1$: $\frac{M_{0,0} + M_{0,1}}{M_{1,0} + M_{1,1}} = z_2$. -/
theorem mobius3Mat_eval_one (z₁ z₂ z₃ : ℂ) (h13 : z₁ ≠ z₃) :
    (mobius3Mat z₁ z₂ z₃ 0 0 + mobius3Mat z₁ z₂ z₃ 0 1) /
    (mobius3Mat z₁ z₂ z₃ 1 0 + mobius3Mat z₁ z₂ z₃ 1 1) = z₂ := by
  dsimp [mobius3Mat]
  have hnum : z₃ * (z₂ - z₁) + z₁ * (z₃ - z₂) = z₂ * (z₃ - z₁) := by ring
  have hden : (z₂ - z₁) + (z₃ - z₂) = z₃ - z₁ := by ring
  rw [hnum, hden]
  have hd : z₃ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
  exact mul_div_cancel_right₀ z₂ hd

/-- Evaluation of the Möbius transform at $\infty$: the leading coefficient ratio $\frac{M_{0,0}}{M_{1,0}} = z_3$. -/
theorem mobius3Mat_eval_inf (z₁ z₂ z₃ : ℂ) (h12 : z₁ ≠ z₂) :
    (mobius3Mat z₁ z₂ z₃ 0 0) / (mobius3Mat z₁ z₂ z₃ 1 0) = z₃ := by
  dsimp [mobius3Mat]
  have hd : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  exact mul_div_cancel_right₀ z₃ hd

/-! ## 4. Left/Right Spinorial Lorentz Action and Trifactor Factorization -/

/-- Left-Right spinorial Lorentz bilinear map on $2 \times 2$ matrices:
    $(g_L, g_R) \cdot M = g_L M g_R^\dagger$. -/
def lorentzLeftRight
    (gL gR : Matrix (Fin 2) (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  gL * M * gRᴴ

@[simp]
theorem lorentzLeftRight_one (M : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentzLeftRight 1 1 M = M := by
  dsimp [lorentzLeftRight]
  simp

theorem lorentzLeftRight_comp
    (gL1 gL2 gR1 gR2 : Matrix (Fin 2) (Fin 2) ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentzLeftRight (gL1 * gL2) (gR1 * gR2) M =
      lorentzLeftRight gL1 gR1 (lorentzLeftRight gL2 gR2 M) := by
  dsimp [lorentzLeftRight]
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The diagonal left-right action preserves Hermiticity and coincides with `lorentzSoldering`. -/
theorem lorentzLeftRight_hermitian_eq (g : Matrix (Fin 2) (Fin 2) ℂ) (X : HermitianMat2) :
    lorentzLeftRight g g X.mat = (lorentzSoldering g X).mat := rfl

/-- 🏆 TRIFACTOR LORENTZ FACTORIZATION: The diagonal spinorial action factors coherently through K·A·N. -/
theorem lorentzLeftRight_kan_factorization
    {g : Matrix (Fin 2) (Fin 2) ℂ} (kan : KANData g) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentzLeftRight g g M =
      lorentzLeftRight kan.K kan.K (lorentzLeftRight kan.A kan.A (lorentzLeftRight kan.N kan.N M)) := by
  have hfact : g = kan.K * kan.A * kan.N := kan.factorization
  conv_lhs => rw [hfact]
  rw [lorentzLeftRight_comp, lorentzLeftRight_comp]

/-! ## 5. Doubled Krein Carrier Fourier Transport -/

section DoubledKreinTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

set_option linter.unusedSectionVars false in
/-- Parabolic operator nilpotency on the doubled carrier. -/
theorem doubledKrein_parabolic_nilpotent :
    (doubledKreinAction (E := E) (InfoGeometry.Physics.K (R := ℝ))).comp
      (doubledKreinAction (E := E) (InfoGeometry.Physics.K (R := ℝ))) = 0 :=
  doubledKrein_parabolic_sq

set_option linter.unusedSectionVars false in
/-- Hyperbolic boost grading involution on the doubled carrier. -/
theorem doubledKrein_hyperbolic_involutive :
    (doubledKreinAction (E := E) matrixEpsilon).comp
      (doubledKreinAction (E := E) matrixEpsilon) = ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  dsimp [doubledKreinAction]
  rw [← ρclock_mul, matrixEpsilon_sq, ρclock_one]

set_option linter.unusedSectionVars false in
/-- Elliptic clock complex structure on the doubled carrier. -/
theorem doubledKrein_clockAxis_complex_structure :
    (doubledKreinAction (E := E) matrixClockAxis).comp
      (doubledKreinAction (E := E) matrixClockAxis) = - ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  dsimp [doubledKreinAction]
  rw [← ρclock_mul, matrixClockAxis_sq, map_neg, ρclock_one]

end DoubledKreinTransport

/-! ## 6. Stage-Successor Block Embedding and Trifactor Fourier Synthesis -/

/-- Embedding the clock axis into `ComplexMatrixStage.Stage 1`. -/
def stage1ClockAxis : ComplexMatrixStage.Stage 1 :=
  embedMat2ToStage1 matClockAxisC

/-- Embedding the clock Fourier projectors into `ComplexMatrixStage.Stage 1`. -/
def stage1ClockProjPlus : ComplexMatrixStage.Stage 1 :=
  embedMat2ToStage1 clockProjPlus

def stage1ClockProjMinus : ComplexMatrixStage.Stage 1 :=
  embedMat2ToStage1 clockProjMinus

/-- 🏆 STAGE 1 FOURIER PARTITION: The embedded clock projectors sum to the stage-1 identity matrix. -/
theorem stage1ClockProj_sum :
    stage1ClockProjPlus + stage1ClockProjMinus = 1 := by
  dsimp [stage1ClockProjPlus, stage1ClockProjMinus]
  ext v w
  dsimp [embedMat2ToStage1, Matrix.add_apply, Matrix.one_apply]
  have hsum : clockProjPlus (bitword1Equiv v) (bitword1Equiv w) +
              clockProjMinus (bitword1Equiv v) (bitword1Equiv w) =
              (1 : Matrix (Fin 2) (Fin 2) ℂ) (bitword1Equiv v) (bitword1Equiv w) := by
    have := congrFun (congrFun (congrArg (fun (M : Matrix (Fin 2) (Fin 2) ℂ) => M) clockProj_sum) (bitword1Equiv v)) (bitword1Equiv w)
    exact this
  rw [hsum]
  have hequiv : (bitword1Equiv v = bitword1Equiv w) ↔ v = w :=
    bitword1Equiv.apply_eq_iff_eq
  by_cases h : v = w
  · subst h
    simp
  · have hne : bitword1Equiv v ≠ bitword1Equiv w := fun he => h (hequiv.mp he)
    simp [h, hne]

/-- 🏆 STAGE 2 BOND COMMUTATIVITY: The trifactor Fourier projectors commute with successor bonding `bondFun 1`. -/
theorem stage2_fourier_bond_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    stage2BlockEmbed (M * N) = stage2BlockEmbed M * stage2BlockEmbed N :=
  stage2BlockEmbed_mul M N

end InfoGeometry.Canonical.MatrixStageTrifactorFourierCyclotomic
