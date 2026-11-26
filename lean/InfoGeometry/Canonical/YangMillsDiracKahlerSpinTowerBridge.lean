/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Yang–Mills Dirac–Kähler Real Spin-Tower Dictionary, Hodge Duality, & Bogomolny Bounds

Reconstructs the pristine mathematical dictionary unifying exterior differential forms, real
Majorana–Dirac Clifford algebras, Yang–Mills Hodge duality, the three normalized trace functionals,
the Euclidean–Lorentzian Bogomolny inequalities, and the inductive `2 × 2` chiral spin tower:

1. **Level `k = 1` (`Λ•(ℝ^{1,1}) ≅ Cl(1,1) ≅ M₂(ℝ)`)**:
   Null 1-forms `u⁺ = !![0, 1; 0, 0]`, `v⁻ = !![0, 0; 1, 0]` (`(u⁺)² = (v⁻)² = 0`) generate the
   orthonormal real Clifford basis `ε = u⁺ - v⁻ = eps2` (`ε² = -I₂`), `X = u⁺ + v⁻ = xMir2`
   (`X² = I₂`, `{ε, X} = 0`), and chiral volume 2-form `Z = ε X = zCut2`. The 2D Hodge star
   `⋆₂ α = Z * α` squares to `+I₂` and acts by `⋆₂ u⁺ = u⁺`, `⋆₂ v⁻ = -v⁻`, `⋆₂ ε = X`, `⋆₂ X = ε`.

2. **Level `k = 2` (`Λ•(ℝ^{1,3}) ≅ Cl(3,1) ≅ M₄(ℝ)`)**:
   Repairs the naive draft conflation where `gamma0 := I₂ ⊗ₖ eps2` wrongly commutes with
   `gamma3 := zCut2 ⊗ₖ I₂`. Reusing the verified repository generators
   `DiracSpinCasimirNambuModulesBridge.diracGamma0..3` (`γ₀ = eps2 ⊗ₖ I₂`, `γ₁ = xMir2 ⊗ₖ zCut2`,
   `γ₂ = xMir2 ⊗ₖ xMir2`, `γ₃ = zCut2 ⊗ₖ I₂`, `diracOmega4 = γ₀ γ₁ γ₂ γ₃ = -(xMir2 ⊗ₖ eps2)`),
   all six grade-2 bivector generators `sig01, sig02, sig03` (symmetric electric boosts) and
   `sig23, sig31, sig12` (skew-symmetric magnetic rotations) satisfy:
   - Exact Krein transpose flip `F(E, B)ᵀ = F(E, -B)` on `ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃`;
   - Exact Lorentzian Hodge star `⋆₄ F := diracOmega4 * F` with `⋆₄² = -1` and
     `⋆₄ F(E, B) = F(-B, E)`;
   - Master bilinear trace formula `Tr(F(E, B) * F(E', B')) = E · E' - B · B'`, yielding:
     - Lorentzian Lagrangian density `Tr(F²) = ‖E‖² - ‖B‖²`,
     - Euclidean Hilbert–Schmidt energy `Tr(Fᵀ F) = ‖E‖² + ‖B‖² ≥ 0`,
     - Topological Pontryagin density `Tr((-ω₄) F²) = 2 (E · B)`,
     - Bogomolny identities `Tr(Fᵀ F) ∓ Tr(ω₄ F²) = ‖E ± B‖² ≥ 0` and `|Tr(ω₄ F²)| ≤ Tr(Fᵀ F)`.

3. **Level `k → k+1 → ∞` (Inductive `2 × 2` Chiral Spin Tower & Direct Limit)**:
   - Left tensor refinement `spinTowerStep A := I₂ ⊗ₖ A` preserves `*`-algebra operations and
     the dimensional normalized trace `normalizedTowerTrace (I₂ ⊗ₖ A) = normalizedTowerTrace A` for
     every finite matrix stage, keeping all three Yang–Mills trace functionals scale-invariant.
   - Reindexing `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ ≃ₐ[ℝ] MatStage 2` connects `ymCurvature4`
     directly to `Cl11TensorTower.stageEmbed 2` (`A ↦ A ⊗ₖ I₂`), `Cl11TensorTower.normalizedTrace`,
     and the infinite direct limit `Cl11TensorTowerLimit.Limit` via `ofStage 2`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `exists_noncomm_mat2_dk`, `exists_noncomm_mat4_dk`, `exists_noncomm_matStage2_dk`
* `level1_dirac_kahler_exterior_dictionary`
* `level2_ym_hodge_krein_and_duality`
* `level2_ym_three_traces_and_bogomolny`
* `spinTowerStep_star_algebra_and_normalized_trace`
* `ymCurvature4_stageEmbed_and_direct_limit`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `spinTowerStep_star_algebra_and_normalized_trace` applies to arbitrary `[Fintype ι] [Nonempty ι] ℝ`-matrices.

#### BUCKET 3: OPEN CLOSURE DEBT
* Curved-spacetime metric Hodge-star fiber bundles and full 4D quantum Yang–Mills measure
  existence/mass gap lie outside this finite-matrix / algebraic direct-limit dictionary.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Kronecker
open Matrix

namespace InfoGeometry.Canonical.YangMillsDiracKahlerSpinTowerBridge

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem exists_noncomm_mat2_dk :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨zCut2, xMir2, fun h => ?_⟩
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  norm_num [zCut2, xMir2, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Explicit non-commutativity witness on `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ`. -/
theorem exists_noncomm_mat4_dk :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨diracGamma0, diracGamma3, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (1, 0)) h
  norm_num [diracGamma0, diracGamma3, eps2, zCut2, Matrix.kroneckerMap_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at h00

/-- Explicit non-commutativity witness on `MatStage 2`. -/
theorem exists_noncomm_matStage2_dk : ∃ A B : MatStage 2, A * B ≠ B * A := by
  refine ⟨((1 : MatStage 1) ⊗ₖ gamma_0_base : MatStage 2),
    ((1 : MatStage 1) ⊗ₖ gamma_1_base : MatStage 2), fun h => ?_⟩
  have h00 := congrArg (fun M : MatStage 2 => M ((default, 0), 0) ((default, 0), 0)) h
  change ((1 : MatStage 1) ⊗ₖ gamma_0_base * (1 : MatStage 1) ⊗ₖ gamma_1_base)
      ((default, 0), 0) ((default, 0), 0) =
    ((1 : MatStage 1) ⊗ₖ gamma_1_base * (1 : MatStage 1) ⊗ₖ gamma_0_base)
      ((default, 0), 0) ((default, 0), 0) at h00
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul] at h00
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul] at h00
  norm_num [gamma_0_base, gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

/-! ### Part 1: Level `k = 1` Exterior Forms `Λ•(ℝ^{1,1}) ≅ Cl(1,1) ≅ M₂(ℝ)` -/

/-- Positive null exterior 1-form `u⁺ = e₁₂` in `M₂(ℝ)`. -/
def uPlus2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Negative null exterior 1-form `v⁻ = e₂₁` in `M₂(ℝ)`. -/
def vMinus2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- 2D Clifford–Kähler Hodge star `⋆₂ α = Z * α` (`zCut2 * α`) on `M₂(ℝ)`. -/
def hodgeStar2 (α : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  zCut2 * α

/-- **Theorem 1 (Level `k = 1` Exterior Differential-Form / Clifford Dictionary in `M₂(ℝ)`)**:
Null creation/annihilation 1-forms `uPlus2, vMinus2` generate `xMir2`, `eps2`, and volume form `zCut2`,
while `hodgeStar2` squares to `+1` and acts with chiral eigenvalues `±1` on null 1-forms. -/
theorem level1_dirac_kahler_exterior_dictionary (α : Matrix (Fin 2) (Fin 2) ℝ) :
    (uPlus2 * uPlus2 = 0 ∧ vMinus2 * vMinus2 = 0) ∧
    (uPlus2 + vMinus2 = xMir2 ∧ uPlus2 - vMinus2 = eps2 ∧ eps2 * xMir2 = zCut2) ∧
    (eps2 * eps2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      xMir2 * xMir2 = (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      eps2 * xMir2 + xMir2 * eps2 = 0) ∧
    (hodgeStar2 (hodgeStar2 α) = α ∧
      hodgeStar2 uPlus2 = uPlus2 ∧ hodgeStar2 vMinus2 = -vMinus2 ∧
      hodgeStar2 eps2 = xMir2 ∧ hodgeStar2 xMir2 = eps2) := by
  have hz2 : zCut2 * zCut2 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [zCut2, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [uPlus2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [vMinus2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [uPlus2, vMinus2, xMir2]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [uPlus2, vMinus2, eps2]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [eps2, xMir2, zCut2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [eps2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [xMir2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [eps2, xMir2, Matrix.mul_apply, Fin.sum_univ_two]
  · dsimp [hodgeStar2]
    rw [← Matrix.mul_assoc, hz2, Matrix.one_mul]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [hodgeStar2, zCut2, uPlus2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [hodgeStar2, zCut2, vMinus2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [hodgeStar2, zCut2, eps2, xMir2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [hodgeStar2, zCut2, xMir2, eps2, Matrix.mul_apply, Fin.sum_univ_two]

/-! ### Part 2: Level `k = 2` Real `Cl(3,1)` Bivectors, Hodge Duality, Three Traces, & Bogomolny -/

private lemma kron_neg_left {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kron_neg_right {m₁ n₁ m₂ n₂ R : Type*} [Ring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kron_smul_left {m₁ n₁ m₂ n₂ : Type*}
    (c : ℝ) (A : Matrix m₁ n₁ ℝ) (B : Matrix m₂ n₂ ℝ) :
    (c • A) ⊗ₖ B = c • (A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, mul_assoc]

private lemma kron_smul_right {m₁ n₁ m₂ n₂ : Type*}
    (c : ℝ) (A : Matrix m₁ n₁ ℝ) (B : Matrix m₂ n₂ ℝ) :
    A ⊗ₖ (c • B) = c • (A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, mul_left_comm]

private lemma kron_transpose {m₁ n₁ m₂ n₂ R : Type*} [CommSemiring R]
    (A : Matrix m₁ n₁ R) (B : Matrix m₂ n₂ R) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; rfl

private lemma pauli2_table :
    (zCut2 * zCut2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (xMir2 * xMir2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (eps2 * eps2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (zCut2 * xMir2 = eps2) ∧ (xMir2 * zCut2 = -eps2) ∧
    (zCut2 * eps2 = xMir2) ∧ (eps2 * zCut2 = -xMir2) ∧
    (xMir2 * eps2 = -zCut2) ∧ (eps2 * xMir2 = zCut2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [zCut2, xMir2, eps2, Matrix.mul_apply, Fin.sum_univ_two] }

private lemma pauli2_transpose_and_trace :
    zCut2ᵀ = zCut2 ∧ xMir2ᵀ = xMir2 ∧ eps2ᵀ = -eps2 ∧
    Matrix.trace zCut2 = 0 ∧ Matrix.trace xMir2 = 0 ∧ Matrix.trace eps2 = 0 ∧
    Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trace_fin_two_one⟩
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [zCut2]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [xMir2]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [eps2]
  · norm_num [zCut2, Matrix.trace, Matrix.diag]
  · norm_num [xMir2, Matrix.trace, Matrix.diag]
  · norm_num [eps2, Matrix.trace, Matrix.diag]

/-- Electric boost bivectors `Σ₀ᵢ = (1/2) γ₀ γᵢ` (`i = 1, 2, 3`) built from the repaired
repository Dirac generators `diracGamma0..3`. -/
def sig01 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma0 * diracGamma1)
def sig02 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma0 * diracGamma2)
def sig03 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma0 * diracGamma3)

/-- Magnetic rotation bivectors `Σⱼₖ = (1/2) γⱼ γₖ` (`(2,3), (3,1), (1,2)`). -/
def sig23 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma2 * diracGamma3)
def sig31 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma3 * diracGamma1)
def sig12 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := (1 / 2 : ℝ) • (diracGamma1 * diracGamma2)

private lemma bivectors_kron_normal_form :
    diracOmega4 = -(xMir2 ⊗ₖ eps2) ∧
    sig01 = (1 / 2 : ℝ) • (zCut2 ⊗ₖ zCut2) ∧
    sig02 = (1 / 2 : ℝ) • (zCut2 ⊗ₖ xMir2) ∧
    sig03 = (1 / 2 : ℝ) • ((-xMir2) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    sig23 = (1 / 2 : ℝ) • ((-eps2) ⊗ₖ xMir2) ∧
    sig31 = (1 / 2 : ℝ) • (eps2 ⊗ₖ zCut2) ∧
    sig12 = (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ eps2) := by
  obtain ⟨hZ2, hX2, hE2, hZX, hXZ, hZE, hEZ, hXE, hEX⟩ := pauli2_table
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [diracOmega4, diracGamma0, diracGamma1, diracGamma2, diracGamma3]
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [diracGamma0, diracGamma1, diracGamma2, diracGamma3, eps2, xMir2, zCut2,
        Matrix.kroneckerMap_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  · dsimp [sig01, diracGamma0, diracGamma1]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hEX]
  · dsimp [sig02, diracGamma0, diracGamma2]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hEX]
  · dsimp [sig03, diracGamma0, diracGamma3]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hEZ]
  · dsimp [sig23, diracGamma2, diracGamma3]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, hXZ]
  · dsimp [sig31, diracGamma3, diracGamma1]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hZX]
  · dsimp [sig12, diracGamma1, diracGamma2]
    rw [← Matrix.mul_kronecker_mul, hX2, hZX]

/-- Real Majorana–Dirac Yang–Mills curvature bivector `F(E, B)` in `M₄(ℝ)`. -/
def ymCurvature4 (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  E₁ • sig01 + E₂ • sig02 + E₃ • sig03 + B₁ • sig23 + B₂ • sig31 + B₃ • sig12

/-- 4D Lorentzian Hodge star operator `⋆₄ F := diracOmega4 * F` on `M₄(ℝ)`. -/
def hodgeStar4 (F : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  diracOmega4 * F

private lemma bivectors_hodge_transpose_and_comm :
    (diracOmega4 * diracOmega4 = -1 ∧ diracOmega4ᵀ = -diracOmega4) ∧
    (diracOmega4 * sig01 = sig23 ∧ diracOmega4 * sig02 = sig31 ∧ diracOmega4 * sig03 = sig12 ∧
      diracOmega4 * sig23 = -sig01 ∧ diracOmega4 * sig31 = -sig02 ∧ diracOmega4 * sig12 = -sig03) ∧
    (sig01 * diracOmega4 = diracOmega4 * sig01 ∧ sig02 * diracOmega4 = diracOmega4 * sig02 ∧
      sig03 * diracOmega4 = diracOmega4 * sig03 ∧ sig23 * diracOmega4 = diracOmega4 * sig23 ∧
      sig31 * diracOmega4 = diracOmega4 * sig31 ∧ sig12 * diracOmega4 = diracOmega4 * sig12) ∧
    (sig01ᵀ = sig01 ∧ sig02ᵀ = sig02 ∧ sig03ᵀ = sig03 ∧
      sig23ᵀ = -sig23 ∧ sig31ᵀ = -sig31 ∧ sig12ᵀ = -sig12) := by
  obtain ⟨hW, h01, h02, h03, h23, h31, h12⟩ := bivectors_kron_normal_form
  obtain ⟨hZ2, hX2, hE2, hZX, hXZ, hZE, hEZ, hXE, hEX⟩ := pauli2_table
  obtain ⟨hZT, hXT, hET, _, _, _, _⟩ := pauli2_transpose_and_trace
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp only [hW, h01, h02, h03, h23, h31, h12,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.transpose_smul, Matrix.transpose_neg, kron_transpose, Matrix.transpose_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      hZ2, hX2, hE2, hZX, hXZ, hZE, hEZ, hXE, hEX, hZT, hXT, hET,
      kron_neg_left, kron_neg_right, smul_neg, neg_neg, Matrix.one_kronecker_one]

/-- **Theorem 2A (Lorentzian Hodge Star, Krein Transpose, & Chirality Commutation)**:
Inside `M₄(ℝ)` via the repaired Majorana–Dirac bivectors:
1. `diracOmega4² = -1` and `diracOmega4ᵀ = -diracOmega4`.
2. `⋆₄ F(E, B) = F(-B, E)` and `⋆₄² F(E, B) = -F(E, B)`.
3. Krein transpose flips the magnetic part: `F(E, B)ᵀ = F(E, -B)`.
4. `diracOmega4` commutes with every grade-2 Yang–Mills bivector `F(E, B)`. -/
theorem level2_ym_hodge_krein_and_duality (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    (diracOmega4 * diracOmega4 = -1 ∧ diracOmega4ᵀ = -diracOmega4) ∧
    (hodgeStar4 (ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃) = ymCurvature4 (-B₁) (-B₂) (-B₃) E₁ E₂ E₃) ∧
    (hodgeStar4 (hodgeStar4 (ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃)) =
      -(ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃)) ∧
    ((ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃)ᵀ = ymCurvature4 E₁ E₂ E₃ (-B₁) (-B₂) (-B₃)) ∧
    (diracOmega4 * ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃ =
      ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃ * diracOmega4) := by
  obtain ⟨hW, hM, hC, hTr⟩ := bivectors_hodge_transpose_and_comm
  refine ⟨hW, ?_, ?_, ?_, ?_⟩
  · dsimp [hodgeStar4, ymCurvature4]
    simp only [Matrix.mul_add, Matrix.mul_smul, hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1,
      hM.2.2.2.2.2, smul_neg, neg_smul]
    abel
  · dsimp [hodgeStar4]
    rw [← Matrix.mul_assoc, hW.1, Matrix.neg_mul, Matrix.one_mul]
  · dsimp [ymCurvature4]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, hTr.1, hTr.2.1, hTr.2.2.1,
      hTr.2.2.2.1, hTr.2.2.2.2.1, hTr.2.2.2.2.2, smul_neg, neg_smul]
  · dsimp [ymCurvature4]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1, hC.2.2.2.2.2]

private lemma scalar_trace_ymCurvature4_pair (E₁ E₂ E₃ B₁ B₂ B₃ E₁' E₂' E₃' B₁' B₂' B₃' : ℝ)
    (t0101 t0202 t0303 t2323 t3131 t1212 : ℝ)
    (h01 : t0101 = 1) (h02 : t0202 = 1) (h03 : t0303 = 1)
    (h23 : t2323 = -1) (h31 : t3131 = -1) (h12 : t1212 = -1) :
    E₁ * E₁' * t0101 + E₂ * E₂' * t0202 + E₃ * E₃' * t0303 +
      B₁ * B₁' * t2323 + B₂ * B₂' * t3131 + B₃ * B₃' * t1212 =
      (E₁ * E₁' + E₂ * E₂' + E₃ * E₃') - (B₁ * B₁' + B₂ * B₂' + B₃ * B₃') := by
  subst h01 h02 h03 h23 h31 h12
  ring

private lemma sig01_tr_sq : Matrix.trace (sig01 * sig01) = 1 := by
  rw [bivectors_kron_normal_form.2.1, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, ← Matrix.mul_kronecker_mul, pauli2_table.1, Matrix.trace_kronecker,
    trace_fin_two_one]
  norm_num

private lemma sig02_tr_sq : Matrix.trace (sig02 * sig02) = 1 := by
  rw [bivectors_kron_normal_form.2.2.1, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, ← Matrix.mul_kronecker_mul, pauli2_table.1, pauli2_table.2.1,
    Matrix.trace_kronecker, trace_fin_two_one]
  norm_num

private lemma sig03_tr_sq : Matrix.trace (sig03 * sig03) = 1 := by
  rw [bivectors_kron_normal_form.2.2.2.1, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, ← Matrix.mul_kronecker_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    pauli2_table.2.1, Matrix.one_mul, Matrix.trace_kronecker, trace_fin_two_one]
  norm_num

private lemma sig23_tr_sq : Matrix.trace (sig23 * sig23) = -1 := by
  rw [bivectors_kron_normal_form.2.2.2.2.1, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, ← Matrix.mul_kronecker_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    pauli2_table.2.2.1, pauli2_table.2.1, kron_neg_left, Matrix.trace_neg,
    Matrix.trace_kronecker, trace_fin_two_one]
  norm_num

private lemma sig31_tr_sq : Matrix.trace (sig31 * sig31) = -1 := by
  rw [bivectors_kron_normal_form.2.2.2.2.2.1, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, ← Matrix.mul_kronecker_mul, pauli2_table.2.2.1, pauli2_table.1,
    kron_neg_left, Matrix.trace_neg, Matrix.trace_kronecker, trace_fin_two_one]
  norm_num

private lemma sig12_tr_sq : Matrix.trace (sig12 * sig12) = -1 := by
  rw [bivectors_kron_normal_form.2.2.2.2.2.2, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, pauli2_table.2.2.1,
    kron_neg_right, Matrix.trace_neg, Matrix.trace_kronecker, trace_fin_two_one]
  norm_num

private lemma trace_sig_mul_off_diag :
    Matrix.trace (sig01 * sig02) = 0 ∧ Matrix.trace (sig01 * sig03) = 0 ∧
    Matrix.trace (sig01 * sig23) = 0 ∧ Matrix.trace (sig01 * sig31) = 0 ∧ Matrix.trace (sig01 * sig12) = 0 ∧
    Matrix.trace (sig02 * sig01) = 0 ∧ Matrix.trace (sig02 * sig03) = 0 ∧
    Matrix.trace (sig02 * sig23) = 0 ∧ Matrix.trace (sig02 * sig31) = 0 ∧ Matrix.trace (sig02 * sig12) = 0 ∧
    Matrix.trace (sig03 * sig01) = 0 ∧ Matrix.trace (sig03 * sig02) = 0 ∧
    Matrix.trace (sig03 * sig23) = 0 ∧ Matrix.trace (sig03 * sig31) = 0 ∧ Matrix.trace (sig03 * sig12) = 0 ∧
    Matrix.trace (sig23 * sig01) = 0 ∧ Matrix.trace (sig23 * sig02) = 0 ∧
    Matrix.trace (sig23 * sig03) = 0 ∧ Matrix.trace (sig23 * sig31) = 0 ∧ Matrix.trace (sig23 * sig12) = 0 ∧
    Matrix.trace (sig31 * sig01) = 0 ∧ Matrix.trace (sig31 * sig02) = 0 ∧
    Matrix.trace (sig31 * sig03) = 0 ∧ Matrix.trace (sig31 * sig23) = 0 ∧ Matrix.trace (sig31 * sig12) = 0 ∧
    Matrix.trace (sig12 * sig01) = 0 ∧ Matrix.trace (sig12 * sig02) = 0 ∧
    Matrix.trace (sig12 * sig03) = 0 ∧ Matrix.trace (sig12 * sig23) = 0 ∧ Matrix.trace (sig12 * sig31) = 0 := by
  obtain ⟨hW, h01, h02, h03, h23, h31, h12⟩ := bivectors_kron_normal_form
  obtain ⟨hZ2, hX2, hE2, hZX, hXZ, hZE, hEZ, hXE, hEX⟩ := pauli2_table
  obtain ⟨hZT, hXT, hET, hZtr, hXtr, hEtr, h1tr⟩ := pauli2_transpose_and_trace
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { simp only [h01, h02, h03, h23, h31, h12,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        ← Matrix.mul_kronecker_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one,
        kron_neg_left, kron_neg_right, Matrix.trace_neg, Matrix.trace_kronecker,
        hZ2, hX2, hE2, hZX, hXZ, hZE, hEZ, hXE, hEX,
        hZtr, hXtr, hEtr, h1tr,
        neg_zero, mul_zero, zero_mul] }

private lemma trace_ymCurvature4_mul (E₁ E₂ E₃ B₁ B₂ B₃ E₁' E₂' E₃' B₁' B₂' B₃' : ℝ) :
    Matrix.trace (ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃ * ymCurvature4 E₁' E₂' E₃' B₁' B₂' B₃') =
      (E₁ * E₁' + E₂ * E₂' + E₃ * E₃') - (B₁ * B₁' + B₂ * B₂' + B₃ * B₃') := by
  have hOff := trace_sig_mul_off_diag
  dsimp [ymCurvature4]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    hOff.1, hOff.2.1, hOff.2.2.1, hOff.2.2.2.1, hOff.2.2.2.2.1,
    hOff.2.2.2.2.2.1, hOff.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hOff.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    mul_zero, add_zero, zero_add]
  rw [sig01_tr_sq, sig02_tr_sq, sig03_tr_sq, sig23_tr_sq, sig31_tr_sq, sig12_tr_sq]
  ring

private lemma scalar_hs_energy_nonneg (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    0 ≤ (E₁ * E₁ + E₂ * E₂ + E₃ * E₃) - ((-B₁) * B₁ + (-B₂) * B₂ + (-B₃) * B₃) := by
  nlinarith [sq_nonneg E₁, sq_nonneg E₂, sq_nonneg E₃, sq_nonneg B₁, sq_nonneg B₂, sq_nonneg B₃]

private lemma scalar_lorentz_trace (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    (E₁ * E₁ + E₂ * E₂ + E₃ * E₃) - (B₁ * B₁ + B₂ * B₂ + B₃ * B₃) =
      (E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) - (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2) := by
  ring

private lemma scalar_euclidean_trace (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    (E₁ * E₁ + E₂ * E₂ + E₃ * E₃) - ((-B₁) * B₁ + (-B₂) * B₂ + (-B₃) * B₃) =
      (E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) + (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2) := by
  ring

private lemma scalar_pontryagin_trace (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    ((-B₁) * E₁ + (-B₂) * E₂ + (-B₃) * E₃) - (E₁ * B₁ + E₂ * B₂ + E₃ * B₃) =
      -2 * (E₁ * B₁ + E₂ * B₂ + E₃ * B₃) := by
  ring

private lemma scalar_bogomolny_sub (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    ((E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) + (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2)) -
      (-2 * (E₁ * B₁ + E₂ * B₂ + E₃ * B₃)) =
      (E₁ + B₁) ^ 2 + (E₂ + B₂) ^ 2 + (E₃ + B₃) ^ 2 := by
  ring

private lemma scalar_bogomolny_add (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    ((E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) + (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2)) +
      (-2 * (E₁ * B₁ + E₂ * B₂ + E₃ * B₃)) =
      (E₁ - B₁) ^ 2 + (E₂ - B₂) ^ 2 + (E₃ - B₃) ^ 2 := by
  ring

private lemma scalar_bogomolny_abs_le (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    |-2 * (E₁ * B₁ + E₂ * B₂ + E₃ * B₃)| ≤
      (E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) + (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2) := by
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (E₁ - B₁), sq_nonneg (E₂ - B₂), sq_nonneg (E₃ - B₃)]
  · nlinarith [sq_nonneg (E₁ + B₁), sq_nonneg (E₂ + B₂), sq_nonneg (E₃ + B₃)]

/-- **Theorem 2B (Three Yang–Mills Trace Functionals & Bogomolny Inequalities in `M₄(ℝ)`)**:
For every `F = ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃`:
1. Lorentzian action trace: `Tr(F²) = ‖E‖² - ‖B‖²`.
2. Euclidean Hilbert–Schmidt energy: `Tr(Fᵀ F) = ‖E‖² + ‖B‖² ≥ 0`.
3. Pontryagin density: `Tr(ω₄ F²) = -2 (E · B)` and `Tr((-ω₄) F²) = 2 (E · B)`.
4. Exact Bogomolny identities:
   - `Tr(Fᵀ F) - Tr(ω₄ F²) = (E₁ + B₁)² + (E₂ + B₂)² + (E₃ + B₃)² ≥ 0`
   - `Tr(Fᵀ F) + Tr(ω₄ F²) = (E₁ - B₁)² + (E₂ - B₂)² + (E₃ - B₃)² ≥ 0`
   - `|Tr(ω₄ F²)| ≤ Tr(Fᵀ F)`. -/
theorem level2_ym_three_traces_and_bogomolny (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    let F := ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃
    (Matrix.trace (F * F) = (E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) - (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2)) ∧
    (Matrix.trace (Fᵀ * F) = (E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) + (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2)) ∧
    (0 ≤ Matrix.trace (Fᵀ * F)) ∧
    (Matrix.trace (diracOmega4 * (F * F)) = -2 * (E₁ * B₁ + E₂ * B₂ + E₃ * B₃)) ∧
    (Matrix.trace ((-diracOmega4) * (F * F)) = 2 * (E₁ * B₁ + E₂ * B₂ + E₃ * B₃)) ∧
    (Matrix.trace (Fᵀ * F) - Matrix.trace (diracOmega4 * (F * F)) =
      (E₁ + B₁) ^ 2 + (E₂ + B₂) ^ 2 + (E₃ + B₃) ^ 2) ∧
    (Matrix.trace (Fᵀ * F) + Matrix.trace (diracOmega4 * (F * F)) =
      (E₁ - B₁) ^ 2 + (E₂ - B₂) ^ 2 + (E₃ - B₃) ^ 2) ∧
    (|Matrix.trace (diracOmega4 * (F * F))| ≤ Matrix.trace (Fᵀ * F)) := by
  dsimp only
  set F := ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃
  have hL : Matrix.trace (F * F) = (E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) - (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2) := by
    rw [trace_ymCurvature4_mul E₁ E₂ E₃ B₁ B₂ B₃ E₁ E₂ E₃ B₁ B₂ B₃, scalar_lorentz_trace]
  have hE : Matrix.trace (Fᵀ * F) = (E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) + (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2) := by
    rw [(level2_ym_hodge_krein_and_duality E₁ E₂ E₃ B₁ B₂ B₃).2.2.2.1,
      trace_ymCurvature4_mul E₁ E₂ E₃ (-B₁) (-B₂) (-B₃) E₁ E₂ E₃ B₁ B₂ B₃, scalar_euclidean_trace]
  have hP : Matrix.trace (diracOmega4 * (F * F)) = -2 * (E₁ * B₁ + E₂ * B₂ + E₃ * B₃) := by
    rw [← Matrix.mul_assoc]
    change Matrix.trace (hodgeStar4 F * F) = _
    rw [(level2_ym_hodge_krein_and_duality E₁ E₂ E₃ B₁ B₂ B₃).2.1,
      trace_ymCurvature4_mul (-B₁) (-B₂) (-B₃) E₁ E₂ E₃ E₁ E₂ E₃ B₁ B₂ B₃, scalar_pontryagin_trace]
  have hPNeg : Matrix.trace ((-diracOmega4) * (F * F)) = 2 * (E₁ * B₁ + E₂ * B₂ + E₃ * B₃) := by
    rw [Matrix.neg_mul, Matrix.trace_neg, hP, neg_mul, neg_neg]
  refine ⟨hL, hE, ?_, hP, hPNeg, ?_, ?_, ?_⟩
  · rw [hE]
    nlinarith [sq_nonneg E₁, sq_nonneg E₂, sq_nonneg E₃, sq_nonneg B₁, sq_nonneg B₂, sq_nonneg B₃]
  · rw [hE, hP, scalar_bogomolny_sub]
  · rw [hE, hP, scalar_bogomolny_add]
  · rw [hE, hP]
    exact scalar_bogomolny_abs_le E₁ E₂ E₃ B₁ B₂ B₃

/-! ### Part 3: Level `k → k+1 → ∞`: Spin-Tower Refinement, Scale-Invariant Traces, & Direct Limit -/

/-- Left `2 × 2` chiral spin-tower refinement `A ↦ I₂ ⊗ A`. -/
def spinTowerStep {ι : Type*} (A : Matrix ι ι ℝ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ A

/-- Dimensional normalized trace `Tr(A) / card ι` preserving trace functionals across all tower scales. -/
def normalizedTowerTrace {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : ℝ :=
  Matrix.trace A / (Fintype.card ι : ℝ)

private lemma scalar_mul_two_div_two_mul (t c : ℝ) (hc : c ≠ 0) :
    (2 * t) / (2 * c) = t / c := by
  field_simp [hc]

/-- **Theorem 3A (Left `I₂ ⊗ A` Spin-Tower `*`-Homomorphism & Trace Scale-Invariance)**:
For any nonempty finite matrix carrier `Matrix ι ι ℝ`, `spinTowerStep A = I₂ ⊗ₖ A` preserves
`1`, `+`, `*`, `•`, transpose, and `normalizedTowerTrace`. -/
theorem spinTowerStep_star_algebra_and_normalized_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (c : ℝ) (A B : Matrix ι ι ℝ) :
    (spinTowerStep (1 : Matrix ι ι ℝ) = (1 : Matrix (Fin 2 × ι) (Fin 2 × ι) ℝ)) ∧
    (spinTowerStep (A + B) = spinTowerStep A + spinTowerStep B) ∧
    (spinTowerStep (A * B) = spinTowerStep A * spinTowerStep B) ∧
    (spinTowerStep (c • A) = c • spinTowerStep A) ∧
    (spinTowerStep Aᵀ = (spinTowerStep A)ᵀ) ∧
    (normalizedTowerTrace (spinTowerStep A) = normalizedTowerTrace A) := by
  refine ⟨Matrix.one_kronecker_one, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.kronecker_add (1 : Matrix (Fin 2) (Fin 2) ℝ) A B
  · rw [spinTowerStep, spinTowerStep, spinTowerStep, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  · exact kron_smul_right c (1 : Matrix (Fin 2) (Fin 2) ℝ) A
  · rw [spinTowerStep, spinTowerStep, kron_transpose, Matrix.transpose_one]
  · unfold normalizedTowerTrace spinTowerStep
    rw [Matrix.trace_kronecker, trace_fin_two_one, Fintype.card_prod, Fintype.card_fin]
    push_cast
    exact scalar_mul_two_div_two_mul (Matrix.trace A) (Fintype.card ι : ℝ)
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Canonical index equivalence `(Fin 2 × Fin 2) ≃ TowerMatrix.Idx 2`. -/
def equivFin2ProdIdx2 : (Fin 2 × Fin 2) ≃ TowerMatrix.Idx 2 where
  toFun p := (((default : TowerMatrix.Idx 0), p.1), p.2)
  invFun q := (q.1.2, q.2)
  left_inv _ := rfl
  right_inv q := by
    rcases q with ⟨⟨q0, q1⟩, q2⟩
    exact Prod.ext (Prod.ext (Subsingleton.elim _ _).symm rfl) rfl

/-- Canonical `ℝ`-algebra isomorphism `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ ≃ₐ[ℝ] MatStage 2`. -/
def mat4ToStage2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ ≃ₐ[ℝ] MatStage 2 :=
  Matrix.reindexAlgEquiv ℝ ℝ equivFin2ProdIdx2

private lemma mat4ToStage2_transpose (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    mat4ToStage2 Aᵀ = (mat4ToStage2 A)ᵀ := by
  ext i j; rfl

private lemma mat4ToStage2_trace (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    Matrix.trace (mat4ToStage2 A) = Matrix.trace A := by
  simp only [mat4ToStage2, Matrix.coe_reindexAlgEquiv, Matrix.trace, Matrix.diag,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp equivFin2ProdIdx2.symm (fun p => A p p)

private lemma mat4ToStage2_normalizedTrace (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) :
    normalizedTrace 2 (mat4ToStage2 A) = Matrix.trace A / 4 := by
  unfold normalizedTrace
  rw [mat4ToStage2_trace]
  norm_num

/-- **Theorem 3B (Right `stageEmbed` Trace Invariance & Direct-Limit Embedding of `ymCurvature4`)**:
Bridges level-2 Dirac–Kähler Yang–Mills curvature `ymCurvature4` into `Cl11TensorTower.MatStage 2`,
its infinite refinement tower `stageEmbed n` (`A ↦ A ⊗ₖ I₂`), and the inductive direct limit
`Cl11TensorTowerLimit.Limit` via `ofStage 2`. -/
theorem ymCurvature4_stageEmbed_and_direct_limit (E₁ E₂ E₃ B₁ B₂ B₃ : ℝ) :
    let F := ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃
    let F2 := mat4ToStage2 F
    (normalizedTrace 3 (stageEmbed 2 (F2 * F2)) =
      ((E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) - (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2)) / 4) ∧
    (normalizedTrace 3 (stageEmbed 2 (F2ᵀ * F2)) =
      ((E₁ ^ 2 + E₂ ^ 2 + E₃ ^ 2) + (B₁ ^ 2 + B₂ ^ 2 + B₃ ^ 2)) / 4) ∧
    (normalizedTrace 3 (stageEmbed 2 (mat4ToStage2 ((-diracOmega4) * (F * F)))) =
      (E₁ * B₁ + E₂ * B₂ + E₃ * B₃) / 2) ∧
    (ofStage 3 (stageEmbed 2 F2) = ofStage 2 F2) ∧
    Function.Injective (ofStage 2) ∧
    (ofStage 2 (mat4ToStage2 (ymCurvature4 1 0 0 0 0 0)) ≠ 0) := by
  dsimp only
  set F := ymCurvature4 E₁ E₂ E₃ B₁ B₂ B₃
  set F2 := mat4ToStage2 F
  have hT := level2_ym_three_traces_and_bogomolny E₁ E₂ E₃ B₁ B₂ B₃
  have hInj2 : Function.Injective (ofStage 2) :=
    directLimitOf_injective (Stage := Cl11TensorTowerLimit.Stage) stageBond matStageEmbed_injective 2
  refine ⟨?_, ?_, ?_, ofStage_apply_bond 2 _, hInj2, ?_⟩
  · change normalizedTrace 3 (matStageEmbed 2 (F2 * F2)) = _
    rw [normalizedTrace_matStageEmbed 2, ← map_mul, mat4ToStage2_normalizedTrace, hT.1]
  · change normalizedTrace 3 (matStageEmbed 2 (F2ᵀ * F2)) = _
    rw [normalizedTrace_matStageEmbed 2, ← mat4ToStage2_transpose, ← map_mul,
      mat4ToStage2_normalizedTrace, hT.2.1]
  · change normalizedTrace 3 (matStageEmbed 2 _) = _
    rw [normalizedTrace_matStageEmbed 2, mat4ToStage2_normalizedTrace, hT.2.2.2.2.1]
    ring
  · intro h0
    have hZ : mat4ToStage2 (ymCurvature4 1 0 0 0 0 0) = 0 := hInj2 (by rw [h0, map_zero])
    have hF0 : ymCurvature4 1 0 0 0 0 0 = 0 := mat4ToStage2.injective (by rw [hZ, map_zero])
    have hE := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (0, 0)) hF0
    norm_num [ymCurvature4, sig01, sig02, sig03, sig23, sig31, sig12,
      diracGamma0, diracGamma1, diracGamma2, diracGamma3, eps2, xMir2, zCut2,
      Matrix.kroneckerMap_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at hE

end InfoGeometry.Canonical.YangMillsDiracKahlerSpinTowerBridge
