/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OsterwalderSchraderPeirceColimitBridge
import InfoGeometry.LLM.KreinPositionalThermodynamicAttention
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Real Chiral Circular Peirce Soldering, Majorana–Dirac `Cl(3,1)`, Vacuum Fiber Determinant & Supercharge Translations

Implements the real `k = 1` `Cl(1,1)` → `k = 2` `Cl(3,1) ≅ M₄(ℝ)` chiral circular soldering
framework without complex `i`, and connects it directly to the codebase's OS/Peirce and Krein
corridors (`OsterwalderSchraderPeirceColimitBridge`, `KreinPositionalThermodynamicAttention`):

1. **Real `Cl(1,1)` Chiral Circular Peirce Basis (`M₂(ℝ)`)**: `pPlus2`, `pMinus2`, `uPlus2`,
   `vMinus2`, cut `zCut2`, mirror `xMir2`, and real symplectic complex-structure replacement `eps2`
   (`eps2² = -1`, `eps2ᵀ = -eps2`, `{Z, X} = {Z, ε} = {X, ε} = 0`).
2. **Real Majorana–Dirac Clifford Algebra (`Cl(3,1) ≅ M₄(ℝ)`)**: `diracGamma0..3` satisfying
   `(X_Dirac)² = (-x₀² + x₁² + x₂² + x₃²) • I₄` and `-(1/4) Tr((X_Dirac)²) = x₀² - x₁² - x₂² - x₃²`.
3. **Real Chiral Circular Pauli Soldering & Fiber Jacobian Determinant**: `realChiralSolderingKron`,
   `realChiralSolderingAdjKron`, `realSoldering4`, and `chiralVacuumFrame4`, proving exact reindexing,
   Clifford–Minkowski contraction, `(x₀² - x₁² - x₂² - x₃²)²` determinant factorization, and vacuum
   frame covariance.
4. **Chiral Supercharges Generating Translation**: nilpotent `superchargeBridgeX`, `superchargeBridgeY`
   whose anticommutator recovers `realSoldering4 p` with null mass-shell `det = 0`, while summing
   two independent supercharge translations gives timelike nonnegativity `(p₀+q₀)² - ‖p+q‖² ≥ 0`.
5. **Repo-Native OS/Peirce & Krein Bridge**: proves `zCut2 = matSigmaZ = eta11 = invS pPlus2`,
   `xMir2 = matSigmaX = invS projGround = boostGen2`, and
   `lorentzBoost2 η = (1/2) • transferMatHyp η = cosh η • 1 + sinh η • xMir2`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `real_chiral_circular_peirce_laws`
* `real_majorana_dirac_interval`
* `real_chiral_soldering_and_vacuum_fiber_det`
* `chiral_supercharge_anticommutator_translation`
* `zCut2_eq_matSigmaZ`, `zCut2_eq_eta11`, `xMir2_eq_matSigmaX`, `xMir2_eq_invS_projGround`,
  `xMir2_eq_boostGen2`, `invS_pPlus2_eq_zCut2`, `lorentzBoost2_eq_cosh_add_sinh_xMir2`,
  `transferMatHyp_half_eq_cosh_add_sinh_xMir2`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* None (all identities hold unconditionally over `ℝ`).

#### BUCKET 3: OPEN CLOSURE DEBT
* Lifting these finite-matrix `k = 1, 2` Majorana–Dirac / soldering identities to curved Lorentzian
  spin-connection bundles and continuum 4D quantum gauge dynamics remains outside this finite module.
-/

noncomputable section

open scoped BigOperators Kronecker
open Matrix

namespace InfoGeometry.Canonical.RealChiralDiracSolderingBridge

open InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap
open InfoGeometry.OperatorAlgebra.OsterwalderSchraderPeirceColimitBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.LLM.KreinPositionalThermodynamicAttention

/-! ### Part 1: Real Cl(1,1) Chiral Circular Peirce Basis of M₂(ℝ) (Zero Complex i) -/

def pPlus2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def pMinus2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 1]
def uPlus2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def vMinus2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- Real Cl(1,1) cut `Z = P₊ - P₋`, mirror `X = u⁺ + v⁻`, and symplectic circular `i`
replacement `ε = u⁺ - v⁻` (`ε² = -1`, zero complex `i`). -/
def zCut2 : Matrix (Fin 2) (Fin 2) ℝ := pPlus2 - pMinus2
def xMir2 : Matrix (Fin 2) (Fin 2) ℝ := uPlus2 + vMinus2
def eps2 : Matrix (Fin 2) (Fin 2) ℝ := uPlus2 - vMinus2

/-- **Theorem 1 (Chiral Circular Peirce Basis & Realified `i` Laws)**. -/
theorem real_chiral_circular_peirce_laws :
    pPlus2 * pPlus2 = pPlus2 ∧
    pMinus2 * pMinus2 = pMinus2 ∧
    pPlus2 * pMinus2 = 0 ∧
    pPlus2 + pMinus2 = 1 ∧
    pPlus2 * uPlus2 = uPlus2 ∧
    uPlus2 * pMinus2 = uPlus2 ∧
    pMinus2 * vMinus2 = vMinus2 ∧
    vMinus2 * pPlus2 = vMinus2 ∧
    uPlus2 * uPlus2 = 0 ∧
    vMinus2 * vMinus2 = 0 ∧
    uPlus2 * vMinus2 = pPlus2 ∧
    vMinus2 * uPlus2 = pMinus2 ∧
    eps2 * eps2 = -1 ∧
    eps2ᵀ = -eps2 ∧
    zCut2 * zCut2 = 1 ∧
    xMir2 * xMir2 = 1 ∧
    zCut2 * xMir2 + xMir2 * zCut2 = 0 ∧
    zCut2 * eps2 + eps2 * zCut2 = 0 ∧
    xMir2 * eps2 + eps2 * xMir2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.neg_apply,
        Matrix.transpose_apply, Matrix.one_apply, Matrix.zero_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        dsimp [pPlus2, pMinus2, uPlus2, vMinus2, zCut2, xMir2, eps2] <;> norm_num }

/-! ### Part 2: Real Majorana–Dirac Clifford Algebra Cl(3,1) ≅ M₄(ℝ) -/

/-- Real Majorana–Dirac matrices in `M₄(ℝ) ≅ M₂(ℝ) ⊗ M₂(ℝ)` constructed purely from the
`k = 1` Cl(1,1) circular Peirce atom (`γ₀² = -1`, `γ₁² = γ₂² = γ₃² = +1`). -/
def diracGamma0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := eps2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
def diracGamma1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := xMir2 ⊗ₖ zCut2
def diracGamma2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := xMir2 ⊗ₖ xMir2
def diracGamma3 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := zCut2 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)

private lemma kronecker_add_left' {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A₁ A₂ : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) :
    (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [add_mul]

private lemma kronecker_add_right' {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B₁ B₂ : Matrix m₂ n₂ R) :
    A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [mul_add]

private lemma kronecker_neg_left' {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [neg_mul]

private lemma scalar_dirac_trace_eq (x₀ x₁ x₂ x₃ : ℝ) :
    -(1 / 4 : ℝ) * ((-x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) * (2 * 2 : ℕ)) =
      x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by
  norm_num
  ring

/-- **Theorem 2 (Real Cl(3,1) Majorana–Dirac Algebra & Signed Lorentzian Trace-Square)**:
For any real 4-vector `(x₀, x₁, x₂, x₃) ∈ ℝ⁴`, `X_Dirac = x₀ γ₀ + x₁ γ₁ + x₂ γ₂ + x₃ γ₃`
satisfies `(X_Dirac)² = (-x₀² + x₁² + x₂² + x₃²) • I₄` and `-(1/4) Tr((X_Dirac)²) = x₀² - x₁² - x₂² - x₃²`. -/
theorem real_majorana_dirac_interval (x₀ x₁ x₂ x₃ : ℝ) :
    let X := x₀ • diracGamma0 + x₁ • diracGamma1 + x₂ • diracGamma2 + x₃ • diracGamma3
    X * X = (-x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) ∧
    -(1 / 4 : ℝ) * Matrix.trace (X * X) = x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by
  have hL := real_chiral_circular_peirce_laws
  have hE2 := hL.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hZ2 := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hX2 := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hZX := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hZE := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hXE := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have h00 : diracGamma0 * diracGamma0 = -1 := by
    dsimp [diracGamma0]
    rw [← Matrix.mul_kronecker_mul, hE2, Matrix.one_mul, kronecker_neg_left',
      Matrix.one_kronecker_one]
  have h11 : diracGamma1 * diracGamma1 = 1 := by
    dsimp [diracGamma1]
    rw [← Matrix.mul_kronecker_mul, hX2, hZ2, Matrix.one_kronecker_one]
  have h22 : diracGamma2 * diracGamma2 = 1 := by
    dsimp [diracGamma2]
    rw [← Matrix.mul_kronecker_mul, hX2, Matrix.one_kronecker_one]
  have h33 : diracGamma3 * diracGamma3 = 1 := by
    dsimp [diracGamma3]
    rw [← Matrix.mul_kronecker_mul, hZ2, Matrix.one_mul, Matrix.one_kronecker_one]
  have h01 : diracGamma0 * diracGamma1 + diracGamma1 * diracGamma0 = 0 := by
    dsimp [diracGamma0, diracGamma1]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      ← kronecker_add_left', add_comm (eps2 * xMir2), hXE, Matrix.zero_kronecker]
  have h02 : diracGamma0 * diracGamma2 + diracGamma2 * diracGamma0 = 0 := by
    dsimp [diracGamma0, diracGamma2]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      ← kronecker_add_left', add_comm (eps2 * xMir2), hXE, Matrix.zero_kronecker]
  have h03 : diracGamma0 * diracGamma3 + diracGamma3 * diracGamma0 = 0 := by
    dsimp [diracGamma0, diracGamma3]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      ← kronecker_add_left', add_comm (eps2 * zCut2), hZE, Matrix.zero_kronecker]
  have h12 : diracGamma1 * diracGamma2 + diracGamma2 * diracGamma1 = 0 := by
    dsimp [diracGamma1, diracGamma2]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hX2,
      ← kronecker_add_right', hZX, Matrix.kronecker_zero]
  have h13 : diracGamma1 * diracGamma3 + diracGamma3 * diracGamma1 = 0 := by
    dsimp [diracGamma1, diracGamma3]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← kronecker_add_left', add_comm (xMir2 * zCut2), hZX, Matrix.zero_kronecker]
  have h23 : diracGamma2 * diracGamma3 + diracGamma3 * diracGamma2 = 0 := by
    dsimp [diracGamma2, diracGamma3]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← kronecker_add_left', add_comm (xMir2 * zCut2), hZX, Matrix.zero_kronecker]
  have hAnti01 : diracGamma1 * diracGamma0 = -(diracGamma0 * diracGamma1) :=
    eq_neg_of_add_eq_zero_right h01
  have hAnti02 : diracGamma2 * diracGamma0 = -(diracGamma0 * diracGamma2) :=
    eq_neg_of_add_eq_zero_right h02
  have hAnti03 : diracGamma3 * diracGamma0 = -(diracGamma0 * diracGamma3) :=
    eq_neg_of_add_eq_zero_right h03
  have hAnti12 : diracGamma2 * diracGamma1 = -(diracGamma1 * diracGamma2) :=
    eq_neg_of_add_eq_zero_right h12
  have hAnti13 : diracGamma3 * diracGamma1 = -(diracGamma1 * diracGamma3) :=
    eq_neg_of_add_eq_zero_right h13
  have hAnti23 : diracGamma3 * diracGamma2 = -(diracGamma2 * diracGamma3) :=
    eq_neg_of_add_eq_zero_right h23
  dsimp
  have hSq :
      (x₀ • diracGamma0 + x₁ • diracGamma1 + x₂ • diracGamma2 + x₃ • diracGamma3) *
      (x₀ • diracGamma0 + x₁ • diracGamma1 + x₂ • diracGamma2 + x₃ • diracGamma3) =
      (-x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    rw [h00, h11, h22, h33, hAnti01, hAnti02, hAnti03, hAnti12, hAnti13, hAnti23]
    simp only [smul_neg]
    module
  refine ⟨hSq, ?_⟩
  rw [hSq, Matrix.trace_smul, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin]
  rw [smul_eq_mul]
  exact scalar_dirac_trace_eq x₀ x₁ x₂ x₃

/-! ### Part 3: Real Chiral Circular Pauli Soldering, Fiber Jacobian Determinant, & Vacuum Frame -/

/-- Realified chiral circular Pauli soldering operator on `Fin 2 × Fin 2` replacing complex `i`
by `eps2`. -/
def realChiralSolderingKron (x₀ x₁ x₂ x₃ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  pPlus2 ⊗ₖ ((x₀ + x₃) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
  pMinus2 ⊗ₖ ((x₀ - x₃) • 1) +
  uPlus2 ⊗ₖ (x₁ • 1 + x₂ • eps2) +
  vMinus2 ⊗ₖ (x₁ • 1 - x₂ • eps2)

/-- Mirror adjugate real soldering operator `M̃(x)` obtained by parity/mirror reversal. -/
def realChiralSolderingAdjKron (x₀ x₁ x₂ x₃ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  pPlus2 ⊗ₖ ((x₀ - x₃) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) +
  pMinus2 ⊗ₖ ((x₀ + x₃) • 1) +
  uPlus2 ⊗ₖ (-(x₁ • 1 + x₂ • eps2)) +
  vMinus2 ⊗ₖ (-(x₁ • 1 - x₂ • eps2))

/-- Explicit `Fin 4 × Fin 4` coordinate form of the real chiral circular soldering matrix. -/
def realSoldering4 (x₀ x₁ x₂ x₃ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![x₀ + x₃, 0,       x₁,      x₂;
     0,       x₀ + x₃, -x₂,     x₁;
     x₁,      -x₂,     x₀ - x₃, 0;
     x₂,      x₁,      0,       x₀ - x₃]

/-- Chiral circular vacuum-frame deformation acting on the 4-dimensional real spinor fiber. -/
def chiralVacuumFrame4 (α₀ α₁ β₀ β₁ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![α₀,  α₁, 0,   0;
     -α₁, α₀, 0,   0;
     0,   0,  β₀,  β₁;
     0,   0,  -β₁, β₀]

private lemma scalar_minkowski_diag (x₀ x₁ x₂ x₃ : ℝ) :
    (x₀ + x₃) * (x₀ - x₃) - x₁ * x₁ - x₂ * x₂ = x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by
  ring

private lemma scalar_minkowski_off1 (x₀ x₁ x₂ x₃ : ℝ) :
    (x₀ + x₃) * (-x₁) + x₁ * (x₀ + x₃) + (-x₂) * 0 + x₂ * 0 = 0 := by
  ring

private lemma scalar_minkowski_off2 (x₀ x₁ x₂ x₃ : ℝ) :
    (x₀ + x₃) * (-x₂) + x₂ * (x₀ + x₃) + x₁ * 0 = 0 := by
  ring

private lemma scalar_minkowski_off3 (x₀ x₁ _x₂ x₃ : ℝ) :
    (x₀ - x₃) * (-x₁) + x₁ * (x₀ - x₃) = 0 := by
  ring

private lemma scalar_minkowski_off4 (x₀ _x₁ x₂ x₃ : ℝ) :
    (x₀ - x₃) * x₂ + (-x₂) * (x₀ - x₃) = 0 := by
  ring

private lemma scalar_minkowski_diag_top (x₀ x₁ x₂ x₃ : ℝ) :
    (x₀ + x₃) * (x₀ - x₃) + (-(x₁ * x₁) + -(x₂ * x₂)) = x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by
  ring

private lemma scalar_minkowski_diag_bot (x₀ x₁ x₂ x₃ : ℝ) :
    -(x₂ * x₂) + -(x₁ * x₁) + (x₀ - x₃) * (x₀ + x₃) = x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by
  ring

private lemma det_fin_four_formula (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.det =
      M 0 0 * (M 1 1 * M 2 2 * M 3 3 - M 1 1 * M 2 3 * M 3 2 -
        M 1 2 * M 2 1 * M 3 3 + M 1 2 * M 2 3 * M 3 1 +
        M 1 3 * M 2 1 * M 3 2 - M 1 3 * M 2 2 * M 3 1) +
      (-1 : ℝ) * M 0 1 * (M 1 0 * M 2 2 * M 3 3 - M 1 0 * M 2 3 * M 3 2 -
        M 1 2 * M 2 0 * M 3 3 + M 1 2 * M 2 3 * M 3 0 +
        M 1 3 * M 2 0 * M 3 2 - M 1 3 * M 2 2 * M 3 0) +
      M 0 2 * (M 1 0 * M 2 1 * M 3 3 - M 1 0 * M 2 3 * M 3 1 -
        M 1 1 * M 2 0 * M 3 3 + M 1 1 * M 2 3 * M 3 0 +
        M 1 3 * M 2 0 * M 3 1 - M 1 3 * M 2 1 * M 3 0) +
      (-1 : ℝ) * M 0 3 * (M 1 0 * M 2 1 * M 3 2 - M 1 0 * M 2 2 * M 3 1 -
        M 1 1 * M 2 0 * M 3 2 + M 1 1 * M 2 2 * M 3 0 +
        M 1 2 * M 2 0 * M 3 1 - M 1 2 * M 2 1 * M 3 0) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.val_zero, Fin.val_one, Fin.val_two,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, pow_zero, pow_one, one_mul]
  have hp2 : (-1 : ℝ) ^ (2 : ℕ) = 1 := by norm_num
  have hp3 : (-1 : ℝ) ^ (3 : ℕ) = -1 := by norm_num
  have hs2 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl
  have ha00 : (0 : Fin 4).succAbove 0 = 1 := rfl
  have ha01 : (0 : Fin 4).succAbove 1 = 2 := rfl
  have ha02 : (0 : Fin 4).succAbove 2 = 3 := rfl
  have ha10 : (1 : Fin 4).succAbove 0 = 0 := rfl
  have ha11 : (1 : Fin 4).succAbove 1 = 2 := rfl
  have ha12 : (1 : Fin 4).succAbove 2 = 3 := rfl
  have ha20 : (2 : Fin 4).succAbove 0 = 0 := rfl
  have ha21 : (2 : Fin 4).succAbove 1 = 1 := rfl
  have ha22 : (2 : Fin 4).succAbove 2 = 3 := rfl
  have ha30 : (3 : Fin 4).succAbove 0 = 0 := rfl
  have ha31 : (3 : Fin 4).succAbove 1 = 1 := rfl
  have ha32 : (3 : Fin 4).succAbove 2 = 2 := rfl
  have hv3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [hv3, hp2, hp3, hs2, ha00, ha01, ha02, ha10, ha11, ha12, ha20, ha21, ha22, ha30, ha31, ha32]
  simp only [one_mul]

private lemma scalar_det_soldering4_expand (x₀ x₁ x₂ x₃ : ℝ) :
    (x₀ + x₃) * ((x₀ + x₃) * (x₀ - x₃) * (x₀ - x₃) - (x₀ + x₃) * 0 * 0 -
        (-x₂) * (-x₂) * (x₀ - x₃) + (-x₂) * 0 * x₁ +
        x₁ * (-x₂) * 0 - x₁ * (x₀ - x₃) * x₁) +
      (-1 : ℝ) * 0 * (0 * (x₀ - x₃) * (x₀ - x₃) - 0 * 0 * 0 -
        (-x₂) * x₁ * (x₀ - x₃) + (-x₂) * 0 * x₂ +
        x₁ * x₁ * 0 - x₁ * (x₀ - x₃) * x₂) +
      x₁ * (0 * (-x₂) * (x₀ - x₃) - 0 * 0 * x₁ -
        (x₀ + x₃) * x₁ * (x₀ - x₃) + (x₀ + x₃) * 0 * x₂ +
        x₁ * x₁ * x₁ - x₁ * (-x₂) * x₂) +
      (-1 : ℝ) * x₂ * (0 * (-x₂) * 0 - 0 * (x₀ - x₃) * x₁ -
        (x₀ + x₃) * x₁ * 0 + (x₀ + x₃) * (x₀ - x₃) * x₂ +
        (-x₂) * x₁ * x₁ - (-x₂) * (-x₂) * x₂) =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) ^ 2 := by
  ring

private lemma scalar_det_vac4_expand (α₀ α₁ β₀ β₁ : ℝ) :
    α₀ * (α₀ * β₀ * β₀ - α₀ * β₁ * (-β₁) - 0 * 0 * β₀ + 0 * β₁ * 0 + 0 * 0 * (-β₁) - 0 * β₀ * 0) +
      (-1 : ℝ) * α₁ * ((-α₁) * β₀ * β₀ - (-α₁) * β₁ * (-β₁) - 0 * 0 * β₀ + 0 * β₁ * 0 + 0 * 0 * (-β₁) - 0 * β₀ * 0) +
      0 * ((-α₁) * 0 * β₀ - (-α₁) * β₁ * 0 - α₀ * 0 * β₀ + α₀ * β₁ * 0 + 0 * 0 * 0 - 0 * 0 * 0) +
      (-1 : ℝ) * 0 * ((-α₁) * 0 * (-β₁) - (-α₁) * β₀ * 0 - α₀ * 0 * (-β₁) + α₀ * β₀ * 0 + 0 * 0 * 0 - 0 * 0 * 0) =
      (α₀ ^ 2 + α₁ ^ 2) * (β₀ ^ 2 + β₁ ^ 2) := by
  ring

private lemma scalar_det_conj_mul (α₀ α₁ β₀ β₁ x₀ x₁ x₂ x₃ : ℝ) :
    ((α₀ ^ 2 + α₁ ^ 2) * (β₀ ^ 2 + β₁ ^ 2)) *
        ((x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) ^ 2) *
        ((α₀ ^ 2 + α₁ ^ 2) * (β₀ ^ 2 + β₁ ^ 2)) =
      ((α₀ ^ 2 + α₁ ^ 2) * (β₀ ^ 2 + β₁ ^ 2)) ^ 2 *
        (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) ^ 2 := by
  ring

/-- **Theorem 3 (Real Chiral Soldering Contraction, Fiber Jacobian Determinant, & Vacuum Deformation)**. -/
theorem real_chiral_soldering_and_vacuum_fiber_det (x₀ x₁ x₂ x₃ α₀ α₁ β₀ β₁ : ℝ) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv (realChiralSolderingKron x₀ x₁ x₂ x₃) =
      realSoldering4 x₀ x₁ x₂ x₃) ∧
    (realChiralSolderingKron x₀ x₁ x₂ x₃ * realChiralSolderingAdjKron x₀ x₁ x₂ x₃ =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)) ∧
    (realSoldering4 x₀ x₁ x₂ x₃).det = (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) ^ 2 ∧
    (chiralVacuumFrame4 α₀ α₁ β₀ β₁).det = (α₀ ^ 2 + α₁ ^ 2) * (β₀ ^ 2 + β₁ ^ 2) ∧
    (chiralVacuumFrame4 α₀ α₁ β₀ β₁ * realSoldering4 x₀ x₁ x₂ x₃ *
      (chiralVacuumFrame4 α₀ α₁ β₀ β₁)ᵀ).det =
      ((α₀ ^ 2 + α₁ ^ 2) * (β₀ ^ 2 + β₁ ^ 2)) ^ 2 * (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) ^ 2 := by
  have hReidx : Matrix.reindex finProdFinEquiv finProdFinEquiv
      (realChiralSolderingKron x₀ x₁ x₂ x₃) = realSoldering4 x₀ x₁ x₂ x₃ := by
    have hs0 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 0 = (0, 0) := by decide
    have hs1 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 1 = (0, 1) := by decide
    have hs2 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 2 = (1, 0) := by decide
    have hs3 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 3 = (1, 1) := by decide
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.reindex_apply, hs0, hs1, hs2, hs3, realChiralSolderingKron, realSoldering4,
        pPlus2, pMinus2, uPlus2, vMinus2, eps2]
  have hMul : realChiralSolderingKron x₀ x₁ x₂ x₃ * realChiralSolderingAdjKron x₀ x₁ x₂ x₃ =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) •
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        realChiralSolderingKron, realChiralSolderingAdjKron,
        pPlus2, pMinus2, uPlus2, vMinus2, eps2]
    all_goals first
      | exact scalar_minkowski_diag_top x₀ x₁ x₂ x₃
      | exact scalar_minkowski_diag_bot x₀ x₁ x₂ x₃
      | exact scalar_minkowski_diag x₀ x₁ x₂ x₃
      | exact scalar_minkowski_off1 x₀ x₁ x₂ x₃
      | exact scalar_minkowski_off2 x₀ x₁ x₂ x₃
      | exact scalar_minkowski_off3 x₀ x₁ x₂ x₃
      | exact scalar_minkowski_off4 x₀ x₁ x₂ x₃
      | ring
  have hDetSold : (realSoldering4 x₀ x₁ x₂ x₃).det = (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) ^ 2 := by
    rw [det_fin_four_formula]
    dsimp [realSoldering4]
    exact scalar_det_soldering4_expand x₀ x₁ x₂ x₃
  have hDetVac : (chiralVacuumFrame4 α₀ α₁ β₀ β₁).det =
      (α₀ ^ 2 + α₁ ^ 2) * (β₀ ^ 2 + β₁ ^ 2) := by
    rw [det_fin_four_formula]
    dsimp [chiralVacuumFrame4]
    exact scalar_det_vac4_expand α₀ α₁ β₀ β₁
  refine ⟨hReidx, hMul, hDetSold, hDetVac, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hDetSold, hDetVac]
  exact scalar_det_conj_mul α₀ α₁ β₀ β₁ x₀ x₁ x₂ x₃

/-! ### Part 4: Chiral Supercharges Generating Translation in the Real Circular Basis -/

/-- A realified chiral spinor pair `(Ξ₁, Ξ₂)` living in `span_ℝ(I₂, ε) ⊂ M₂(ℝ)`. -/
def chiralSpinorFiber (a₁ b₁ a₂ b₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ :=
  (a₁ • 1 + b₁ • eps2, a₂ • 1 + b₂ • eps2)

/-- Off-diagonal Peirce supercharge bridge `X_SUSY` across the `N₊ ↔ N₋` cut in `M₈(ℝ)`. -/
def superchargeBridgeX (a₁ b₁ a₂ b₂ : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  uPlus2 ⊗ₖ !![a₁, b₁, 0, 0;
                -b₁, a₁, 0, 0;
                a₂, b₂, 0, 0;
                -b₂, a₂, 0, 0]

/-- Off-diagonal Peirce supercharge bridge `Y_SUSY = X_SUSYᵀ` across the `N₋ ↔ N₊` cut. -/
def superchargeBridgeY (a₁ b₁ a₂ b₂ : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  vMinus2 ⊗ₖ !![a₁, -b₁, a₂, -b₂;
                 b₁,  a₁, b₂,  a₂;
                 0,   0,  0,   0;
                 0,   0,  0,   0]

private lemma scalar_susy_null_shell (a₁ b₁ a₂ b₂ : ℝ) :
    ((a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2) ^ 2 -
      (a₁ * a₂ + b₁ * b₂) ^ 2 - (b₁ * a₂ - a₁ * b₂) ^ 2 -
      ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2) ^ 2 = 0 := by
  ring

private lemma scalar_susy_two_timelike (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ) :
    0 ≤ ((a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2 + (c₁ ^ 2 + d₁ ^ 2 + c₂ ^ 2 + d₂ ^ 2) / 2) ^ 2 -
      ((a₁ * a₂ + b₁ * b₂) + (c₁ * c₂ + d₁ * d₂)) ^ 2 -
      ((b₁ * a₂ - a₁ * b₂) + (d₁ * c₂ - c₁ * d₂)) ^ 2 -
      ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2 + (c₁ ^ 2 + d₁ ^ 2 - c₂ ^ 2 - d₂ ^ 2) / 2) ^ 2 := by
  have hId :
      ((a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2 + (c₁ ^ 2 + d₁ ^ 2 + c₂ ^ 2 + d₂ ^ 2) / 2) ^ 2 -
      ((a₁ * a₂ + b₁ * b₂) + (c₁ * c₂ + d₁ * d₂)) ^ 2 -
      ((b₁ * a₂ - a₁ * b₂) + (d₁ * c₂ - c₁ * d₂)) ^ 2 -
      ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2 + (c₁ ^ 2 + d₁ ^ 2 - c₂ ^ 2 - d₂ ^ 2) / 2) ^ 2 =
      (a₁ * c₂ - b₁ * d₂ - a₂ * c₁ + b₂ * d₁) ^ 2 +
      (a₁ * d₂ + b₁ * c₂ - a₂ * d₁ - b₂ * c₁) ^ 2 := by
    ring
  rw [hId]
  positivity

private lemma scalar_susy_block_top (a₁ b₁ a₂ b₂ : ℝ) :
    a₁ * a₁ + b₁ * b₁ = (a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2 + (a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2 := by
  ring

private lemma scalar_susy_block_bot (a₁ b₁ a₂ b₂ : ℝ) :
    a₂ * a₂ + b₂ * b₂ = (a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2 - (a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2 := by
  ring

private lemma scalar_susy_off_pos (a₁ b₁ a₂ b₂ : ℝ) :
    a₁ * a₂ + (-b₁) * (-b₂) = a₁ * a₂ + b₁ * b₂ := by
  ring

private lemma scalar_susy_off_neg (a₁ b₁ a₂ b₂ : ℝ) :
    (-b₁) * a₂ + a₁ * b₂ = -(b₁ * a₂ - a₁ * b₂) := by
  ring

private lemma scalar_susy_off_pos2 (a₁ b₁ a₂ b₂ : ℝ) :
    a₁ * (-b₂) + b₁ * a₂ = b₁ * a₂ - a₁ * b₂ := by
  ring

private lemma scalar_susy_off_pos3 (a₁ b₁ a₂ b₂ : ℝ) :
    a₂ * a₁ + b₂ * b₁ = a₁ * a₂ + b₁ * b₂ := by
  ring

private lemma scalar_susy_off_neg2 (a₁ b₁ a₂ b₂ : ℝ) :
    a₂ * (-b₁) + b₂ * a₁ = -(b₁ * a₂ - a₁ * b₂) := by
  ring

private lemma scalar_susy_off_pos4 (a₁ b₁ a₂ b₂ : ℝ) :
    (-b₂) * a₁ + a₂ * b₁ = b₁ * a₂ - a₁ * b₂ := by
  ring

/-- Explicit `Fin 2` non-commutativity witness for `zCut2` and `xMir2`. -/
theorem exists_noncomm_mat2_chiral :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨zCut2, xMir2, fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h01
  dsimp [zCut2, xMir2, pPlus2, pMinus2, uPlus2, vMinus2] at h01
  norm_num at h01

/-- Explicit `Fin 2 × Fin 2` non-commutativity witness for `diracGamma0` and `diracGamma1`. -/
theorem exists_noncomm_mat2x2_dirac :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨diracGamma0, diracGamma1, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (0, 0)) h
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, diracGamma0, diracGamma1,
    Matrix.kronecker_apply] at h00
  dsimp [eps2, xMir2, zCut2, pPlus2, pMinus2, uPlus2, vMinus2] at h00
  norm_num at h00

/-- Explicit `Fin 4` non-commutativity witness between `realSoldering4` and `chiralVacuumFrame4`. -/
theorem exists_noncomm_mat4_soldering :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨realSoldering4 0 1 0 0, chiralVacuumFrame4 1 0 0 0, fun h => ?_⟩
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) h
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at h02
  dsimp [realSoldering4, chiralVacuumFrame4] at h02
  norm_num at h02

/-- Explicit `Fin 2 × Fin 4` non-commutativity witness for `superchargeBridgeX` and `superchargeBridgeY`. -/
theorem exists_noncomm_mat2x4_susy :
    ∃ A B : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨superchargeBridgeX 1 0 0 0, superchargeBridgeY 1 0 0 0, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ => M (0, 0) (0, 0)) h
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four,
    superchargeBridgeX, superchargeBridgeY, Matrix.kronecker_apply] at h00
  dsimp [uPlus2, vMinus2] at h00
  norm_num at h00

/-- **Theorem 4 (Chiral Supercharge Anticommutator Generates Real Null Translation)**. -/
theorem chiral_supercharge_anticommutator_translation (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ) :
    let X := superchargeBridgeX a₁ b₁ a₂ b₂
    let Y := superchargeBridgeY a₁ b₁ a₂ b₂
    let p₀ := (a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2
    let p₁ := a₁ * a₂ + b₁ * b₂
    let p₂ := b₁ * a₂ - a₁ * b₂
    let p₃ := (a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2
    let q₀ := (c₁ ^ 2 + d₁ ^ 2 + c₂ ^ 2 + d₂ ^ 2) / 2
    let q₁ := c₁ * c₂ + d₁ * d₂
    let q₂ := d₁ * c₂ - c₁ * d₂
    let q₃ := (c₁ ^ 2 + d₁ ^ 2 - c₂ ^ 2 - d₂ ^ 2) / 2
    X * X = 0 ∧
    Y * Y = 0 ∧
    (∀ i j : Fin 4,
      (X * Y + Y * X) (0, i) (0, j) = realSoldering4 p₀ p₁ p₂ p₃ i j) ∧
    (p₀ ^ 2 - p₁ ^ 2 - p₂ ^ 2 - p₃ ^ 2 = 0) ∧
    ((realSoldering4 p₀ p₁ p₂ p₃).det = 0) ∧
    (0 ≤ (p₀ + q₀) ^ 2 - (p₁ + q₁) ^ 2 - (p₂ + q₂) ^ 2 - (p₃ + q₃) ^ 2) := by
  dsimp
  have hL := real_chiral_circular_peirce_laws
  have hU2 := hL.2.2.2.2.2.2.2.2.1
  have hV2 := hL.2.2.2.2.2.2.2.2.2.1
  have hUV := hL.2.2.2.2.2.2.2.2.2.2.1
  have hVU := hL.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [superchargeBridgeX]
    rw [← Matrix.mul_kronecker_mul, hU2, Matrix.zero_kronecker]
  · dsimp [superchargeBridgeY]
    rw [← Matrix.mul_kronecker_mul, hV2, Matrix.zero_kronecker]
  · intro i j
    let SX : Matrix (Fin 4) (Fin 4) ℝ :=
      !![a₁, b₁, 0, 0; -b₁, a₁, 0, 0; a₂, b₂, 0, 0; -b₂, a₂, 0, 0]
    let SY : Matrix (Fin 4) (Fin 4) ℝ :=
      !![a₁, -b₁, a₂, -b₂; b₁, a₁, b₂, a₂; 0, 0, 0, 0; 0, 0, 0, 0]
    have hXY : superchargeBridgeX a₁ b₁ a₂ b₂ * superchargeBridgeY a₁ b₁ a₂ b₂ +
        superchargeBridgeY a₁ b₁ a₂ b₂ * superchargeBridgeX a₁ b₁ a₂ b₂ =
        pPlus2 ⊗ₖ (SX * SY) + pMinus2 ⊗ₖ (SY * SX) := by
      dsimp [superchargeBridgeX, superchargeBridgeY, SX, SY]
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hUV, hVU]
    have hXY_at := congrArg (fun M : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ => M (0, i) (0, j)) hXY
    rw [← Matrix.add_apply, hXY_at]
    simp only [Matrix.add_apply, Matrix.kronecker_apply]
    simp only [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;> simp [SX, SY, realSoldering4, pPlus2, pMinus2]
    all_goals first
      | exact scalar_susy_block_top a₁ b₁ a₂ b₂
      | exact scalar_susy_block_bot a₁ b₁ a₂ b₂
      | exact scalar_susy_off_pos a₁ b₁ a₂ b₂
      | exact scalar_susy_off_pos2 a₁ b₁ a₂ b₂
      | exact scalar_susy_off_pos3 a₁ b₁ a₂ b₂
      | exact scalar_susy_off_pos4 a₁ b₁ a₂ b₂
      | exact scalar_susy_off_neg a₁ b₁ a₂ b₂
      | exact scalar_susy_off_neg2 a₁ b₁ a₂ b₂
      | ring
  · exact scalar_susy_null_shell a₁ b₁ a₂ b₂
  · rw [(real_chiral_soldering_and_vacuum_fiber_det _ _ _ _ 0 0 0 0).2.2.1,
      scalar_susy_null_shell a₁ b₁ a₂ b₂, zero_pow two_ne_zero]
  · exact scalar_susy_two_timelike a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂

/-! ### Part 5: Repo-Native OS/Peirce & Krein Boost Corridor Bridge -/

theorem zCut2_eq_matSigmaZ : zCut2 = matSigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zCut2, pPlus2, pMinus2, matSigmaZ]

theorem zCut2_eq_eta11 : zCut2 = eta11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zCut2, pPlus2, pMinus2, eta11]

theorem xMir2_eq_matSigmaX : xMir2 = matSigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xMir2, uPlus2, vMinus2, matSigmaX]

theorem xMir2_eq_invS_projGround : xMir2 = invS projGround := by
  rw [xMir2_eq_matSigmaX, invS_projGround_eq_matSigmaX]

theorem xMir2_eq_boostGen2 : xMir2 = boostGen2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xMir2, uPlus2, vMinus2, boostGen2]

theorem invS_pPlus2_eq_zCut2 : invS pPlus2 = zCut2 := by
  ext i j
  unfold invS
  simp only [Matrix.sub_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> dsimp [zCut2, pPlus2, pMinus2] <;> norm_num

/-- Every `SO^+(1,1)` positional Lorentz boost `lorentzBoost2 η` expands in the real chiral Peirce
carrier as `cosh η • 1 + sinh η • xMir2`. -/
theorem lorentzBoost2_eq_cosh_add_sinh_xMir2 (η : ℝ) :
    lorentzBoost2 η = Real.cosh η • 1 + Real.sinh η • xMir2 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> dsimp [lorentzBoost2, xMir2, uPlus2, vMinus2] <;> norm_num

private lemma scalar_half_two_cosh' (J : ℝ) : (1 / 2 : ℝ) * (2 * Real.cosh J) = Real.cosh J := by
  ring

private lemma scalar_half_two_sinh' (J : ℝ) : (1 / 2 : ℝ) * (2 * Real.sinh J) = Real.sinh J := by
  ring

/-- Rescaled hyperbolic two-sheet OS transfer matrix `(1/2) • transferMatHyp J` equals
`cosh J • 1 + sinh J • xMir2`. -/
theorem transferMatHyp_half_eq_cosh_add_sinh_xMir2 (J : ℝ) :
    (1 / 2 : ℝ) • transferMatHyp J = Real.cosh J • 1 + Real.sinh J • xMir2 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> dsimp [transferMatHyp, xMir2, uPlus2, vMinus2] <;> norm_num
  · exact scalar_half_two_cosh' J
  · exact scalar_half_two_sinh' J
  · exact scalar_half_two_sinh' J
  · exact scalar_half_two_cosh' J

/-! ### Part 6: Unified `M₈(ℝ)` Chiral Weyl–Dirac Operator & Supercharge Block Placement -/

/-- Explicit `Fin 4 × Fin 4` coordinate form of the mirror adjugate soldering matrix `M̃₄(x)`. -/
def realSolderingAdj4 (x₀ x₁ x₂ x₃ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![x₀ - x₃, 0,       -x₁,     -x₂;
     0,       x₀ - x₃, x₂,      -x₁;
     -x₁,     x₂,      x₀ + x₃, 0;
     -x₂,     -x₁,     0,       x₀ + x₃]

/-- Realified chiral Weyl–Dirac operator `D(x) = u⁺ ⊗ M₄(x) + v⁻ ⊗ M̃₄(x)` in `M₂(M₄(ℝ)) ≅ M₈(ℝ)`. -/
def weylDirac8 (x₀ x₁ x₂ x₃ : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  uPlus2 ⊗ₖ realSoldering4 x₀ x₁ x₂ x₃ + vMinus2 ⊗ₖ realSolderingAdj4 x₀ x₁ x₂ x₃

/-- Outer chirality grading `Γ₅ = Z ⊗ I₄` on `M₂(M₄(ℝ))`. -/
def gamma5_8 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  zCut2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- Outer sheet-flip mirror `J_mir = X ⊗ I₄` on `M₂(M₄(ℝ))`. -/
def mirror8 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  xMir2 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- Realified 4D spinor fiber complex structure `J₄ = I₂ ⊗ ε` (`J₄² = -I₄`, zero complex `i`). -/
def fiberJ4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,  1, 0,  0;
     -1, 0, 0,  0;
     0,  0, 0,  1;
     0,  0, -1, 0]

/-- Lifted 8D fiber complex structure `J₈ = I₂ ⊗ J₄` (`J₈² = -I₈`). -/
def fiberJ8 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ fiberJ4

/-- Reindexing `realChiralSolderingAdjKron` recovers `realSolderingAdj4`. -/
theorem realChiralSolderingAdjKron_reindex (x₀ x₁ x₂ x₃ : ℝ) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv (realChiralSolderingAdjKron x₀ x₁ x₂ x₃) =
      realSolderingAdj4 x₀ x₁ x₂ x₃ := by
  have hs0 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 0 = (0, 0) := by decide
  have hs1 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 1 = (0, 1) := by decide
  have hs2 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 2 = (1, 0) := by decide
  have hs3 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 3 = (1, 1) := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, hs0, hs1, hs2, hs3, realChiralSolderingAdjKron,
      realSolderingAdj4, pPlus2, pMinus2, uPlus2, vMinus2, eps2]

private lemma scalar_weyl_sq_half (x₀ x₁ x₂ x₃ : ℝ) :
    (1 / 2 : ℝ) * (2 * (x₀ * x₀ - x₁ * x₁ - x₂ * x₂ - x₃ * x₃)) =
      x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by
  ring

private lemma neg_kronecker24 (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kronecker_neg24 (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma reindex_finProd_mul (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    Matrix.reindex finProdFinEquiv finProdFinEquiv A *
      Matrix.reindex finProdFinEquiv finProdFinEquiv B =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (Equiv.sum_comp finProdFinEquiv.symm
    (fun k => A (finProdFinEquiv.symm i) k * B k (finProdFinEquiv.symm j))).symm

private lemma realChiralSolderingKron_add_adj_sym (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℝ) :
    realChiralSolderingKron u₀ u₁ u₂ u₃ * realChiralSolderingAdjKron v₀ v₁ v₂ v₃ +
    realChiralSolderingKron v₀ v₁ v₂ v₃ * realChiralSolderingAdjKron u₀ u₁ u₂ u₃ =
    (2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      realChiralSolderingKron, realChiralSolderingAdjKron,
      pPlus2, pMinus2, uPlus2, vMinus2, eps2] <;>
    ring

private lemma realChiralSolderingAdjKron_add_sym (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℝ) :
    realChiralSolderingAdjKron u₀ u₁ u₂ u₃ * realChiralSolderingKron v₀ v₁ v₂ v₃ +
    realChiralSolderingAdjKron v₀ v₁ v₂ v₃ * realChiralSolderingKron u₀ u₁ u₂ u₃ =
    (2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) •
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      realChiralSolderingKron, realChiralSolderingAdjKron,
      pPlus2, pMinus2, uPlus2, vMinus2, eps2] <;>
    ring

private lemma realSoldering4_mul_adj_sym (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℝ) :
    realSoldering4 u₀ u₁ u₂ u₃ * realSolderingAdj4 v₀ v₁ v₂ v₃ +
    realSoldering4 v₀ v₁ v₂ v₃ * realSolderingAdj4 u₀ u₁ u₂ u₃ =
    (2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hu := (real_chiral_soldering_and_vacuum_fiber_det u₀ u₁ u₂ u₃ 1 0 1 0).1
  have hv := (real_chiral_soldering_and_vacuum_fiber_det v₀ v₁ v₂ v₃ 1 0 1 0).1
  rw [← hu, ← hv, ← realChiralSolderingAdjKron_reindex u₀ u₁ u₂ u₃,
    ← realChiralSolderingAdjKron_reindex v₀ v₁ v₂ v₃,
    reindex_finProd_mul, reindex_finProd_mul]
  have hSym := congrArg (Matrix.reindex finProdFinEquiv finProdFinEquiv)
    (realChiralSolderingKron_add_adj_sym u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃)
  ext i j
  have hij := congrFun (congrFun hSym i) j
  simpa [Matrix.reindex_apply, Matrix.one_apply] using hij

private lemma realSolderingAdj4_mul_sym (u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℝ) :
    realSolderingAdj4 u₀ u₁ u₂ u₃ * realSoldering4 v₀ v₁ v₂ v₃ +
    realSolderingAdj4 v₀ v₁ v₂ v₃ * realSoldering4 u₀ u₁ u₂ u₃ =
    (2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hu := (real_chiral_soldering_and_vacuum_fiber_det u₀ u₁ u₂ u₃ 1 0 1 0).1
  have hv := (real_chiral_soldering_and_vacuum_fiber_det v₀ v₁ v₂ v₃ 1 0 1 0).1
  rw [← hu, ← hv, ← realChiralSolderingAdjKron_reindex u₀ u₁ u₂ u₃,
    ← realChiralSolderingAdjKron_reindex v₀ v₁ v₂ v₃,
    reindex_finProd_mul, reindex_finProd_mul]
  have hSym := congrArg (Matrix.reindex finProdFinEquiv finProdFinEquiv)
    (realChiralSolderingAdjKron_add_sym u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃)
  ext i j
  have hij := congrFun (congrFun hSym i) j
  simpa [Matrix.reindex_apply, Matrix.one_apply] using hij

private lemma susy_block4_eq (a₁ b₁ a₂ b₂ : ℝ) :
    !![a₁, b₁, 0, 0; -b₁, a₁, 0, 0; a₂, b₂, 0, 0; -b₂, a₂, 0, 0] *
    !![a₁, -b₁, a₂, -b₂; b₁, a₁, b₂, a₂; 0, 0, 0, 0; 0, 0, 0, 0] =
    realSoldering4 ((a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2)
      (a₁ * a₂ + b₁ * b₂) (b₁ * a₂ - a₁ * b₂)
      ((a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSoldering4, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first
    | exact scalar_susy_block_top a₁ b₁ a₂ b₂
    | exact scalar_susy_block_bot a₁ b₁ a₂ b₂
    | exact scalar_susy_off_pos a₁ b₁ a₂ b₂
    | exact scalar_susy_off_pos2 a₁ b₁ a₂ b₂
    | exact scalar_susy_off_pos3 a₁ b₁ a₂ b₂
    | exact scalar_susy_off_pos4 a₁ b₁ a₂ b₂
    | exact scalar_susy_off_neg a₁ b₁ a₂ b₂
    | exact scalar_susy_off_neg2 a₁ b₁ a₂ b₂
    | ring

/-- **Theorem 5 (Unifying Parts 3 & 4 in `M₈(ℝ)`: Chiral Weyl–Dirac Clifford Algebra & SUSY Block Placement)**:
1. Chirality and fiber complex structure: `Γ₅² = I₈`, `{Γ₅, D(x)} = 0`, `J₈² = -I₈`, and `[J₈, D(x)] = 0`.
2. **Realified Weyl–Dirac Interval**: `D(x)² = (x₀² - x₁² - x₂² - x₃²) • I₈`.
3. **Polarized Clifford Anticommutator**: `D(x) D(y) + D(y) D(x) = 2(x₀ y₀ - x₁ y₁ - x₂ y₂ - x₃ y₃) • I₈`.
4. **Unified SUSY Translation Placement**: Projecting `{X_SUSY, Y_SUSY}` onto `P₊ ⊗ I₄` equals the
   upper-right chiral block of `D(p)` under `J_mir`. -/
theorem unified_weyl_dirac8_and_susy_block (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ a₁ b₁ a₂ b₂ : ℝ) :
    let D := weylDirac8 x₀ x₁ x₂ x₃
    let Dy := weylDirac8 y₀ y₁ y₂ y₃
    let Pplus8 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ := pPlus2 ⊗ₖ 1
    let X := superchargeBridgeX a₁ b₁ a₂ b₂
    let Y := superchargeBridgeY a₁ b₁ a₂ b₂
    let p₀ := (a₁ ^ 2 + b₁ ^ 2 + a₂ ^ 2 + b₂ ^ 2) / 2
    let p₁ := a₁ * a₂ + b₁ * b₂
    let p₂ := b₁ * a₂ - a₁ * b₂
    let p₃ := (a₁ ^ 2 + b₁ ^ 2 - a₂ ^ 2 - b₂ ^ 2) / 2
    gamma5_8 * gamma5_8 = 1 ∧
    gamma5_8 * D + D * gamma5_8 = 0 ∧
    fiberJ8 * fiberJ8 = -1 ∧
    fiberJ8 * D = D * fiberJ8 ∧
    D * D = (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) •
      (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) ∧
    D * Dy + Dy * D = (2 * (x₀ * y₀ - x₁ * y₁ - x₂ * y₂ - x₃ * y₃)) •
      (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) ∧
    Pplus8 * (X * Y + Y * X) * Pplus8 = Pplus8 * weylDirac8 p₀ p₁ p₂ p₃ * mirror8 := by
  have hPol : ∀ u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ : ℝ,
      weylDirac8 u₀ u₁ u₂ u₃ * weylDirac8 v₀ v₁ v₂ v₃ +
      weylDirac8 v₀ v₁ v₂ v₃ * weylDirac8 u₀ u₁ u₂ u₃ =
      (2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) •
        (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) := by
    intro u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃
    have hL := real_chiral_circular_peirce_laws
    have hPsum := hL.2.2.2.1
    have hU2 := hL.2.2.2.2.2.2.2.2.1
    have hV2 := hL.2.2.2.2.2.2.2.2.2.1
    have hUV := hL.2.2.2.2.2.2.2.2.2.2.1
    have hVU := hL.2.2.2.2.2.2.2.2.2.2.2.1
    dsimp [weylDirac8]
    simp only [add_mul, mul_add, ← Matrix.mul_kronecker_mul,
      hU2, hV2, hUV, hVU, Matrix.zero_kronecker, zero_add, add_zero]
    calc (pMinus2 ⊗ₖ (realSolderingAdj4 u₀ u₁ u₂ u₃ * realSoldering4 v₀ v₁ v₂ v₃) +
          pPlus2 ⊗ₖ (realSoldering4 u₀ u₁ u₂ u₃ * realSolderingAdj4 v₀ v₁ v₂ v₃)) +
         (pMinus2 ⊗ₖ (realSolderingAdj4 v₀ v₁ v₂ v₃ * realSoldering4 u₀ u₁ u₂ u₃) +
          pPlus2 ⊗ₖ (realSoldering4 v₀ v₁ v₂ v₃ * realSolderingAdj4 u₀ u₁ u₂ u₃))
        = pPlus2 ⊗ₖ (realSoldering4 u₀ u₁ u₂ u₃ * realSolderingAdj4 v₀ v₁ v₂ v₃ +
            realSoldering4 v₀ v₁ v₂ v₃ * realSolderingAdj4 u₀ u₁ u₂ u₃) +
          pMinus2 ⊗ₖ (realSolderingAdj4 u₀ u₁ u₂ u₃ * realSoldering4 v₀ v₁ v₂ v₃ +
            realSolderingAdj4 v₀ v₁ v₂ v₃ * realSoldering4 u₀ u₁ u₂ u₃) := by
            simp only [Matrix.kronecker_add]; abel
      _ = pPlus2 ⊗ₖ ((2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) •
            (1 : Matrix (Fin 4) (Fin 4) ℝ)) +
          pMinus2 ⊗ₖ ((2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) •
            (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
            rw [realSoldering4_mul_adj_sym u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃,
              realSolderingAdj4_mul_sym u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃]
      _ = (2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) •
            ((pPlus2 + pMinus2) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
            simp only [Matrix.kronecker_smul, ← smul_add, ← Matrix.add_kronecker]
      _ = (2 * (u₀ * v₀ - u₁ * v₁ - u₂ * v₂ - u₃ * v₃)) •
            (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) := by
            rw [hPsum, Matrix.one_kronecker_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, hPol x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃, ?_⟩
  · dsimp [gamma5_8]
    rw [← Matrix.mul_kronecker_mul, real_chiral_circular_peirce_laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      one_mul, Matrix.one_kronecker_one]
  · dsimp [gamma5_8, weylDirac8]
    have hZU : zCut2 * uPlus2 = uPlus2 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [zCut2, pPlus2, pMinus2, uPlus2, Matrix.mul_apply, Fin.sum_univ_two]
    have hUZ : uPlus2 * zCut2 = -uPlus2 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [zCut2, pPlus2, pMinus2, uPlus2, Matrix.mul_apply, Fin.sum_univ_two]
    have hZV : zCut2 * vMinus2 = -vMinus2 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [zCut2, pPlus2, pMinus2, vMinus2, Matrix.mul_apply, Fin.sum_univ_two]
    have hVZ : vMinus2 * zCut2 = vMinus2 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [zCut2, pPlus2, pMinus2, vMinus2, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [mul_add, add_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one]
    rw [hZU, hUZ, hZV, hVZ, neg_kronecker24, neg_kronecker24]
    abel
  · have hJ4 : fiberJ4 * fiberJ4 = -1 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [fiberJ4, Matrix.mul_apply, Fin.sum_univ_four]
    dsimp [fiberJ8]
    rw [← Matrix.mul_kronecker_mul, one_mul, hJ4, kronecker_neg24, Matrix.one_kronecker_one]
  · have hJ4Sold : fiberJ4 * realSoldering4 x₀ x₁ x₂ x₃ = realSoldering4 x₀ x₁ x₂ x₃ * fiberJ4 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [fiberJ4, realSoldering4, Matrix.mul_apply, Fin.sum_univ_four]
    have hJ4Adj : fiberJ4 * realSolderingAdj4 x₀ x₁ x₂ x₃ =
        realSolderingAdj4 x₀ x₁ x₂ x₃ * fiberJ4 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [fiberJ4, realSolderingAdj4, Matrix.mul_apply, Fin.sum_univ_four]
    dsimp [fiberJ8, weylDirac8]
    simp only [mul_add, add_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one, hJ4Sold, hJ4Adj]
  · have h2 := hPol x₀ x₁ x₂ x₃ x₀ x₁ x₂ x₃
    have hHalf := congrArg (fun M : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ => (1 / 2 : ℝ) • M) h2
    simp only [← two_smul ℝ, smul_smul, scalar_weyl_sq_half] at hHalf
    have hOne : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    rw [hOne, one_smul] at hHalf
    exact hHalf
  · have hSusy4 := susy_block4_eq a₁ b₁ a₂ b₂
    have hL := real_chiral_circular_peirce_laws
    have hPpUV : pPlus2 * (uPlus2 * vMinus2) * pPlus2 = pPlus2 := by
      rw [hL.2.2.2.2.2.2.2.2.2.2.1, hL.1, hL.1]
    have hPpVU : pPlus2 * (vMinus2 * uPlus2) * pPlus2 = 0 := by
      rw [hL.2.2.2.2.2.2.2.2.2.2.2.1, hL.2.2.1, zero_mul]
    have hPpUX : pPlus2 * uPlus2 * xMir2 = pPlus2 := by
      dsimp [xMir2]
      rw [hL.2.2.2.2.1, mul_add, hL.2.2.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.2.2.2.1, zero_add]
    have hPpVX : pPlus2 * vMinus2 * xMir2 = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [pPlus2, vMinus2, xMir2, uPlus2, Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [superchargeBridgeX, superchargeBridgeY, weylDirac8, mirror8]
    simp only [add_mul, mul_add, ← Matrix.mul_kronecker_mul, one_mul, mul_one,
      hPpUV, hPpVU, hPpUX, hPpVX, Matrix.zero_kronecker, add_zero, hSusy4]

end InfoGeometry.Canonical.RealChiralDiracSolderingBridge
