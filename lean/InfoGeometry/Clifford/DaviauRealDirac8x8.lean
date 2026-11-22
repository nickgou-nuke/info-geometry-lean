/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KreinMajoranaBlockInvariance

/-!
# Daviau (2001) Real 8x8 Dirac Algebra, Quaternionic Commutant, and `so(8) + sym(8)` Split

Formalizes Section 1 and Section 2 of Claude Daviau (2001), *"Vers une mecanique quantique sans
nombre complexe"*, Ann. Fond. Louis de Broglie 26 (n deg special), 149-171:
1. Explicit integer `8 x 8` matrices `{gamma0Z..gamma3Z}` and `{p1Z, p2Z, p3Z}` lifted via
   `(Int.castRingHom ℝ).mapMatrix` to `Mat8R = Matrix (Fin 8) (Fin 8) ℝ` without introducing
   `√(-1)` or `x₄ = i c t`.
2. Clifford relations `{Γ^μ, Γ^ν} = 2 g^{μν} I₈` for `g = diag(1, -1, -1, -1)`, commutant
   relations `[Γ^μ, P_j] = 0`, and quaternion algebra `P_j² = -I₈`, `P₁P₂ = -P₂P₁ = P₃` (Eq. 14).
3. Identification `Γ⁰ = kreinMetric8` (`KreinMajoranaBlockInvariance.kreinMetric8`), Krein
   self-adjointness `(Γ^μ)ᵀ Γ⁰ = Γ⁰ Γ^μ`, and skew-adjointness `P_jᵀ = -P_j` (Eq. 9).
4. The orthogonal transpose splitting `M₈(ℝ) = so(8) ⊕ sym(8)` with explicit Frobenius-orthogonal
   bases (`28 + 36 = 64`).
-/

noncomputable section

namespace InfoGeometry.Clifford.DaviauRealDirac8x8

open Matrix
open InfoGeometry.Algebra.FiniteSpin

/-! ### Section 1: Explicit `8 × 8` Integer Matrices & Lifting to `ℝ` -/

/-- Cast a `Mat8Z` matrix entrywise along `Int.castRingHom ℝ` into `Mat8R`. -/
def castZ8 (M : Mat8Z) : Mat8R :=
  (Int.castRingHom ℝ).mapMatrix M

@[simp] theorem castZ8_mul (A B : Mat8Z) : castZ8 (A * B) = castZ8 A * castZ8 B :=
  (Int.castRingHom ℝ).mapMatrix.map_mul A B

@[simp] theorem castZ8_add (A B : Mat8Z) : castZ8 (A + B) = castZ8 A + castZ8 B :=
  (Int.castRingHom ℝ).mapMatrix.map_add A B

@[simp] theorem castZ8_sub (A B : Mat8Z) : castZ8 (A - B) = castZ8 A - castZ8 B :=
  (Int.castRingHom ℝ).mapMatrix.map_sub A B

@[simp] theorem castZ8_neg (A : Mat8Z) : castZ8 (-A) = -castZ8 A :=
  (Int.castRingHom ℝ).mapMatrix.map_neg A

@[simp] theorem castZ8_one : castZ8 (1 : Mat8Z) = (1 : Mat8R) :=
  (Int.castRingHom ℝ).mapMatrix.map_one

@[simp] theorem castZ8_zero : castZ8 (0 : Mat8Z) = (0 : Mat8R) :=
  (Int.castRingHom ℝ).mapMatrix.map_zero

@[simp] theorem castZ8_transpose (A : Mat8Z) : castZ8 Aᵀ = (castZ8 A)ᵀ := rfl

theorem castZ8_zsmul (c : ℤ) (A : Mat8Z) : castZ8 (c • A) = (c : ℝ) • castZ8 A := by
  ext i j; exact Int.cast_mul c (A i j)

@[simp] theorem castZ8_trace (A : Mat8Z) :
    Matrix.trace (castZ8 A) = ((Matrix.trace A : ℤ) : ℝ) := by
  simp [Matrix.trace, Matrix.diag, castZ8]

/-- Daviau real Dirac matrix `Γ⁰ = diag(1,1,1,1,-1,-1,-1,-1)` over `ℤ`. -/
def gamma0Z : Mat8Z :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, -1]

/-- Daviau real Dirac matrix `Γ¹` over `ℤ` (induced by `ψ ↔ Φ` in Daviau Eq. 3). -/
def gamma1Z : Mat8Z :=
  !![0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     -1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0]

/-- Daviau real Dirac matrix `Γ²` over `ℤ` (induced by `ψ ↔ Φ` in Daviau Eq. 3). -/
def gamma2Z : Mat8Z :=
  !![0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     -1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0]

/-- Daviau real Dirac matrix `Γ³` over `ℤ` (induced by `ψ ↔ Φ` in Daviau Eq. 3). -/
def gamma3Z : Mat8Z :=
  !![0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0, 0, 0;
     -1, 0, 0, 0, 0, 0, 0, 0]

/-- First quaternionic commutant operator `P₁` over `ℤ` (Daviau Eq. 12). -/
def p1Z : Mat8Z :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
     -1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 0, 0, 1, 0]

/-- Second quaternionic commutant operator `P₂` over `ℤ` (Daviau Eq. 12). -/
def p2Z : Mat8Z :=
  !![0, 0, -1, 0, 0, 0, 0, 0;
     0, 0, 0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, -1, 0, 0, 0;
     0, 0, 0, 0, 0, -1, 0, 0]

/-- Third quaternionic commutant operator `P₃` over `ℤ` (real representation of `i · I₄`). -/
def p3Z : Mat8Z :=
  !![0, 0, 0, -1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0, 0, 0]

/-- Pseudoscalar volume element `Γ^{0123} = Γ⁰ Γ¹ Γ² Γ³` over `ℤ`. -/
def gamma0123Z : Mat8Z :=
  !![0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, -1;
     -1, 0, 0, 0, 0, 0, 0, 0;
     0, -1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

/-- Indexed real Dirac family `Γ^μ` over `ℤ` (`μ = 0,1,2,3`). -/
def gammaZ : Fin 4 → Mat8Z
  | ⟨0, _⟩ => gamma0Z
  | ⟨1, _⟩ => gamma1Z
  | ⟨2, _⟩ => gamma2Z
  | ⟨3, _⟩ => gamma3Z

/-- Indexed quaternion commutant `{P₁, P₂, P₃}` over `ℤ`. -/
def quatPZ : Fin 3 → Mat8Z
  | ⟨0, _⟩ => p1Z
  | ⟨1, _⟩ => p2Z
  | ⟨2, _⟩ => p3Z

/-- Contravariant Minkowski signature `diag(1, -1, -1, -1)` over `ℤ`. -/
def minkowskiMetricZ : Fin 4 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => -1

/-- Daviau's real `8 × 8` Dirac matrices `Γ^μ ∈ M₈(ℝ)`. -/
def gammaR (μ : Fin 4) : Mat8R := castZ8 (gammaZ μ)

/-- Daviau's real `8 × 8` quaternionic commutant `P_j ∈ M₈(ℝ)` (`j = 0,1,2` for `P₁,P₂,P₃`). -/
def quatPR (j : Fin 3) : Mat8R := castZ8 (quatPZ j)

/-- Real pseudoscalar `Γ^{0123} = Γ⁰ Γ¹ Γ² Γ³ ∈ M₈(ℝ)`. -/
def gamma0123R : Mat8R := castZ8 gamma0123Z

/-- Real Minkowski diagonal metric `g^{μμ} ∈ {+1, -1}`. -/
def minkowskiMetricR (μ : Fin 4) : ℝ := (minkowskiMetricZ μ : ℝ)

/-! ### Section 2: Integer-Kernel Verification & Real Lifting -/

theorem gammaZ_anticomm (μ ν : Fin 4) :
    gammaZ μ * gammaZ ν + gammaZ ν * gammaZ μ =
      (if μ = ν then 2 * minkowskiMetricZ μ else 0) • (1 : Mat8Z) := by
  revert μ ν; decide

theorem gammaZ_comm_quatPZ (μ : Fin 4) (j : Fin 3) :
    gammaZ μ * quatPZ j = quatPZ j * gammaZ μ := by
  revert μ j; decide

theorem quatPZ_sq (j : Fin 3) :
    quatPZ j * quatPZ j = -(1 : Mat8Z) := by
  revert j; decide

theorem quatPZ_01 : p1Z * p2Z = p3Z := by decide
theorem quatPZ_10 : p2Z * p1Z = -p3Z := by decide
theorem quatPZ_12 : p2Z * p3Z = p1Z := by decide
theorem quatPZ_21 : p3Z * p2Z = -p1Z := by decide
theorem quatPZ_20 : p3Z * p1Z = p2Z := by decide
theorem quatPZ_02 : p1Z * p3Z = -p2Z := by decide

theorem gamma0123Z_eq : gamma0Z * gamma1Z * gamma2Z * gamma3Z = gamma0123Z := by decide
theorem gamma0123Z_sq : gamma0123Z * gamma0123Z = -(1 : Mat8Z) := by decide
theorem gamma0123Z_anticomm_gammaZ (μ : Fin 4) :
    gamma0123Z * gammaZ μ + gammaZ μ * gamma0123Z = 0 := by
  revert μ; decide
theorem gamma0123Z_comm_quatPZ (j : Fin 3) :
    gamma0123Z * quatPZ j = quatPZ j * gamma0123Z := by
  revert j; decide

theorem gammaZ_krein_adjoint (μ : Fin 4) :
    (gammaZ μ)ᵀ * gamma0Z = gamma0Z * gammaZ μ := by
  revert μ; decide

theorem quatPZ_transpose (j : Fin 3) :
    (quatPZ j)ᵀ = -quatPZ j := by
  revert j; decide

/-- `{Γ^μ, Γ^ν} = 2 g^{μν} I₈` in `M₈(ℝ)`. -/
theorem gammaR_anticomm (μ ν : Fin 4) :
    gammaR μ * gammaR ν + gammaR ν * gammaR μ =
      (if μ = ν then 2 * minkowskiMetricR μ else 0) • (1 : Mat8R) := by
  dsimp [gammaR]
  rw [← castZ8_mul, ← castZ8_mul, ← castZ8_add, gammaZ_anticomm μ ν, castZ8_zsmul, castZ8_one]
  congr 1
  by_cases h : μ = ν
  · simp [h, minkowskiMetricR]
  · simp [h]

/-- `Γ^μ P_j = P_j Γ^μ` for all `μ : Fin 4`, `j : Fin 3`. -/
theorem gammaR_comm_quatPR (μ : Fin 4) (j : Fin 3) :
    gammaR μ * quatPR j = quatPR j * gammaR μ := by
  dsimp [gammaR, quatPR]
  rw [← castZ8_mul, ← castZ8_mul, gammaZ_comm_quatPZ μ j]

/-- `P_j² = -I₈` in `M₈(ℝ)` (Daviau Eq. 14). -/
theorem quatPR_sq (j : Fin 3) : quatPR j * quatPR j = -(1 : Mat8R) := by
  dsimp [quatPR]; rw [← castZ8_mul, quatPZ_sq j, castZ8_neg, castZ8_one]

/-- Quaternionic multiplication table `{P₁, P₂, P₃}` (Daviau Eq. 14). -/
theorem quatPR_01 : quatPR 0 * quatPR 1 = quatPR 2 := by
  change castZ8 p1Z * castZ8 p2Z = castZ8 p3Z
  rw [← castZ8_mul, quatPZ_01]

theorem quatPR_10 : quatPR 1 * quatPR 0 = -quatPR 2 := by
  change castZ8 p2Z * castZ8 p1Z = -castZ8 p3Z
  rw [← castZ8_mul, quatPZ_10, castZ8_neg]

theorem quatPR_12 : quatPR 1 * quatPR 2 = quatPR 0 := by
  change castZ8 p2Z * castZ8 p3Z = castZ8 p1Z
  rw [← castZ8_mul, quatPZ_12]

theorem quatPR_21 : quatPR 2 * quatPR 1 = -quatPR 0 := by
  change castZ8 p3Z * castZ8 p2Z = -castZ8 p1Z
  rw [← castZ8_mul, quatPZ_21, castZ8_neg]

theorem quatPR_20 : quatPR 2 * quatPR 0 = quatPR 1 := by
  change castZ8 p3Z * castZ8 p1Z = castZ8 p2Z
  rw [← castZ8_mul, quatPZ_20]

theorem quatPR_02 : quatPR 0 * quatPR 2 = -quatPR 1 := by
  change castZ8 p1Z * castZ8 p3Z = -castZ8 p2Z
  rw [← castZ8_mul, quatPZ_02, castZ8_neg]

/-- `Γ⁰` coincides identically with `KreinMajoranaBlockInvariance.kreinMetric8 = diag(I₄, -I₄)`. -/
theorem gamma0R_eq_kreinMetric8 :
    gammaR 0 = InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinMetric8 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaR, gammaZ, gamma0Z, castZ8,
      InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinMetric8]

theorem gamma0123R_eq : gammaR 0 * gammaR 1 * gammaR 2 * gammaR 3 = gamma0123R := by
  change castZ8 gamma0Z * castZ8 gamma1Z * castZ8 gamma2Z * castZ8 gamma3Z = castZ8 gamma0123Z
  rw [← castZ8_mul, ← castZ8_mul, ← castZ8_mul, gamma0123Z_eq]

theorem gamma0123R_sq : gamma0123R * gamma0123R = -(1 : Mat8R) := by
  dsimp [gamma0123R]; rw [← castZ8_mul, gamma0123Z_sq, castZ8_neg, castZ8_one]

theorem gamma0123R_anticomm_gammaR (μ : Fin 4) :
    gamma0123R * gammaR μ + gammaR μ * gamma0123R = 0 := by
  dsimp [gamma0123R, gammaR]
  rw [← castZ8_mul, ← castZ8_mul, ← castZ8_add, gamma0123Z_anticomm_gammaZ μ, castZ8_zero]

theorem gamma0123R_comm_quatPR (j : Fin 3) :
    gamma0123R * quatPR j = quatPR j * gamma0123R := by
  dsimp [gamma0123R, quatPR]
  rw [← castZ8_mul, ← castZ8_mul, gamma0123Z_comm_quatPZ j]

/-- Krein self-adjointness `(Γ^μ)ᵀ Γ⁰ = Γ⁰ Γ^μ` (Daviau Eq. 9). -/
theorem gammaR_krein_adjoint (μ : Fin 4) :
    (gammaR μ)ᵀ * gammaR 0 = gammaR 0 * gammaR μ := by
  change (castZ8 (gammaZ μ))ᵀ * castZ8 gamma0Z = castZ8 gamma0Z * castZ8 (gammaZ μ)
  rw [← castZ8_transpose, ← castZ8_mul, ← castZ8_mul, gammaZ_krein_adjoint μ]

/-- Skew-symmetry `P_jᵀ = -P_j` in `so(8)`. -/
theorem quatPR_transpose (j : Fin 3) : (quatPR j)ᵀ = -quatPR j := by
  dsimp [quatPR]; rw [← castZ8_transpose, quatPZ_transpose j, castZ8_neg]

/-- Non-commutativity ground witnesses on `Mat8R` (OpenGauss T16). -/
theorem daviau_mat8_noncomm :
    gammaR 0 * gammaR 1 ≠ gammaR 1 * gammaR 0 ∧
      quatPR 0 * quatPR 1 ≠ quatPR 1 * quatPR 0 := by
  constructor
  · intro h
    have h05 := congrArg (fun M : Mat8R => M 0 5) h
    simp [gammaR, gammaZ, gamma0Z, gamma1Z, castZ8, Matrix.mul_apply, Fin.sum_univ_eight] at h05
    norm_num at h05
  · intro h
    have h03 := congrArg (fun M : Mat8R => M 0 3) h
    simp [quatPR, quatPZ, p1Z, p2Z, castZ8, Matrix.mul_apply, Fin.sum_univ_eight] at h03
    norm_num at h03

/-! ### Section 3: The `M₈(ℝ) = so(8) ⊕ sym(8)` Transpose Splitting (`64 = 28 + 36`) -/

/-- The 28-dimensional Lie algebra `so(8) = {M ∈ M₈(ℝ) | Mᵀ = -M}` of real skew-symmetric matrices. -/
def so8Submodule : Submodule ℝ Mat8R where
  carrier := {M | Mᵀ = -M}
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    change Aᵀ = -A at hA; change Bᵀ = -B at hB; change (A + B)ᵀ = -(A + B)
    rw [transpose_add, hA, hB]; abel
  smul_mem' c {A} hA := by
    change Aᵀ = -A at hA; change (c • A)ᵀ = -(c • A)
    rw [transpose_smul, hA, smul_neg]

/-- The 36-dimensional subspace `sym(8) = {M ∈ M₈(ℝ) | Mᵀ = M}` of real symmetric matrices. -/
def sym8Submodule : Submodule ℝ Mat8R where
  carrier := {M | Mᵀ = M}
  zero_mem' := by simp
  add_mem' {A B} hA hB := by
    change Aᵀ = A at hA; change Bᵀ = B at hB; change (A + B)ᵀ = A + B
    rw [transpose_add, hA, hB]
  smul_mem' c {A} hA := by
    change Aᵀ = A at hA; change (c • A)ᵀ = c • A
    rw [transpose_smul, hA]

/-- Direct-sum splitting `M₈(ℝ) = so(8) ⊕ sym(8)` (`M = ½(M - Mᵀ) + ½(M + Mᵀ)`). -/
theorem isCompl_so8_sym8 : IsCompl so8Submodule sym8Submodule := by
  constructor
  · rw [disjoint_iff]
    ext M
    simp only [Submodule.mem_inf, Submodule.mem_bot]
    constructor
    · rintro ⟨hSkew, hSym⟩
      change Mᵀ = -M at hSkew
      change Mᵀ = M at hSym
      have hneg : -M = M := hSkew.symm.trans hSym
      have h2 : (2 : ℝ) • M = 0 := by
        calc
          (2 : ℝ) • M = M + M := two_smul ℝ M
          _ = (-M) + M := by rw [hneg]
          _ = 0 := neg_add_cancel M
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    · rintro rfl; simp
  · rw [codisjoint_iff, eq_top_iff]
    intro M _
    rw [Submodule.mem_sup]
    refine ⟨(1 / 2 : ℝ) • (M - Mᵀ), ?_, (1 / 2 : ℝ) • (M + Mᵀ), ?_, ?_⟩
    · show ((1 / 2 : ℝ) • (M - Mᵀ))ᵀ = -((1 / 2 : ℝ) • (M - Mᵀ))
      rw [transpose_smul, transpose_sub, transpose_transpose, ← smul_neg]; congr 1; abel
    · show ((1 / 2 : ℝ) • (M + Mᵀ))ᵀ = (1 / 2 : ℝ) • (M + Mᵀ)
      rw [transpose_smul, transpose_add, transpose_transpose]; congr 1; abel
    · rw [← smul_add]
      calc
        (1 / 2 : ℝ) • ((M - Mᵀ) + (M + Mᵀ)) = (1 / 2 : ℝ) • ((2 : ℝ) • M) := by
          congr 1; rw [two_smul]; abel
        _ = M := by rw [smul_smul]; norm_num

/-- Sparse signed-permutation representation of an `8 × 8` integer matrix (one nonzero entry
`sgn i` at column `col i` in row `i`) for fast kernel verification of the 64-element basis. -/
structure SpMat8Z where
  col : Fin 8 → Fin 8
  sgn : Fin 8 → ℤ

def SpMat8Z.toMat (A : SpMat8Z) : Mat8Z :=
  fun i j => if j = A.col i then A.sgn i else 0

def SpMat8Z.one : SpMat8Z := ⟨id, fun _ => 1⟩

def SpMat8Z.mul (A B : SpMat8Z) : SpMat8Z :=
  ⟨fun i => B.col (A.col i), fun i => A.sgn i * B.sgn (A.col i)⟩

theorem SpMat8Z.toMat_one : SpMat8Z.one.toMat = (1 : Mat8Z) := by
  ext i j
  simp [SpMat8Z.one, SpMat8Z.toMat, Matrix.one_apply, eq_comm]

theorem SpMat8Z.toMat_mul (A B : SpMat8Z) :
    (A.mul B).toMat = A.toMat * B.toMat := by
  ext i j
  simp only [SpMat8Z.mul, SpMat8Z.toMat, Matrix.mul_apply]
  rw [Finset.sum_eq_single (A.col i)]
  · by_cases hj : j = B.col (A.col i) <;> simp [hj]
  · intro b _ hb; simp [hb]
  · intro hm; exact False.elim (hm (Finset.mem_univ _))

theorem SpMat8Z.toMat_transpose_of_inv (A : SpMat8Z) (ε : ℤ)
    (hinv : ∀ i : Fin 8, A.col (A.col i) = i)
    (hsgn : ∀ i : Fin 8, A.sgn (A.col i) = ε * A.sgn i) :
    (A.toMat)ᵀ = ε • A.toMat := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, SpMat8Z.toMat]
  split_ifs with h1 h2 h2
  · rw [h2, hsgn i]
  · exact False.elim (h2 (by rw [h1, hinv j]))
  · exact False.elim (h1 (by rw [h2, hinv i]))
  · rw [mul_zero]

theorem SpMat8Z.toMat_sq_of_inv (A : SpMat8Z) (δ : ℤ)
    (hinv : ∀ i : Fin 8, A.col (A.col i) = i)
    (hsgn : ∀ i : Fin 8, A.sgn i * A.sgn (A.col i) = δ) :
    A.toMat * A.toMat = δ • (1 : Mat8Z) := by
  rw [← SpMat8Z.toMat_mul, ← SpMat8Z.toMat_one]
  ext i j
  simp only [SpMat8Z.mul, SpMat8Z.toMat, SpMat8Z.one, hinv, hsgn,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hj : j = i
  · simp [hj]
  · simp [hj]

private def gamma0Sp : SpMat8Z := ⟨![0, 1, 2, 3, 4, 5, 6, 7], ![1, 1, 1, 1, -1, -1, -1, -1]⟩
private def gamma1Sp : SpMat8Z := ⟨![5, 4, 7, 6, 1, 0, 3, 2], ![1, -1, -1, 1, 1, -1, -1, 1]⟩
private def gamma2Sp : SpMat8Z := ⟨![6, 7, 4, 5, 2, 3, 0, 1], ![1, -1, 1, -1, -1, 1, -1, 1]⟩
private def gamma3Sp : SpMat8Z := ⟨![7, 6, 5, 4, 3, 2, 1, 0], ![1, 1, 1, 1, -1, -1, -1, -1]⟩
private def p1Sp : SpMat8Z := ⟨![1, 0, 3, 2, 5, 4, 7, 6], ![1, -1, -1, 1, 1, -1, -1, 1]⟩
private def p2Sp : SpMat8Z := ⟨![2, 3, 0, 1, 6, 7, 4, 5], ![-1, -1, 1, 1, 1, 1, -1, -1]⟩
private def p3Sp : SpMat8Z := ⟨![3, 2, 1, 0, 7, 6, 5, 4], ![-1, 1, -1, 1, 1, -1, 1, -1]⟩
private def g0123Sp : SpMat8Z := ⟨![4, 5, 6, 7, 0, 1, 2, 3], ![1, 1, -1, -1, -1, -1, 1, 1]⟩

private theorem gamma0Sp_toMat : gamma0Sp.toMat = gamma0Z := by decide
private theorem gamma1Sp_toMat : gamma1Sp.toMat = gamma1Z := by decide
private theorem gamma2Sp_toMat : gamma2Sp.toMat = gamma2Z := by decide
private theorem gamma3Sp_toMat : gamma3Sp.toMat = gamma3Z := by decide
private theorem p1Sp_toMat : p1Sp.toMat = p1Z := by decide
private theorem p2Sp_toMat : p2Sp.toMat = p2Z := by decide
private theorem p3Sp_toMat : p3Sp.toMat = p3Z := by decide
private theorem g0123Sp_toMat : g0123Sp.toMat = gamma0123Z := by decide

private abbrev mkSp2 (A B : SpMat8Z) := A.mul B
private abbrev mkSp3 (A B C : SpMat8Z) := (A.mul B).mul C
private abbrev mkSp4 (A B C D : SpMat8Z) := ((A.mul B).mul C).mul D

private def skewBasis28Sp : Fin 28 → SpMat8Z :=
  ![gamma1Sp, gamma2Sp, gamma3Sp,
    mkSp2 gamma2Sp gamma3Sp, mkSp2 gamma3Sp gamma1Sp, mkSp2 gamma1Sp gamma2Sp,
    mkSp3 gamma0Sp gamma2Sp gamma3Sp, mkSp3 gamma0Sp gamma3Sp gamma1Sp,
    mkSp3 gamma0Sp gamma1Sp gamma2Sp, g0123Sp,
    p1Sp, p2Sp, p3Sp,
    mkSp2 gamma0Sp p1Sp, mkSp2 gamma0Sp p2Sp, mkSp2 gamma0Sp p3Sp,
    mkSp3 gamma0Sp gamma1Sp p1Sp, mkSp3 gamma0Sp gamma1Sp p2Sp, mkSp3 gamma0Sp gamma1Sp p3Sp,
    mkSp3 gamma0Sp gamma2Sp p1Sp, mkSp3 gamma0Sp gamma2Sp p2Sp, mkSp3 gamma0Sp gamma2Sp p3Sp,
    mkSp3 gamma0Sp gamma3Sp p1Sp, mkSp3 gamma0Sp gamma3Sp p2Sp, mkSp3 gamma0Sp gamma3Sp p3Sp,
    mkSp4 gamma1Sp gamma2Sp gamma3Sp p1Sp, mkSp4 gamma1Sp gamma2Sp gamma3Sp p2Sp,
    mkSp4 gamma1Sp gamma2Sp gamma3Sp p3Sp]

private def symBasis36Sp : Fin 36 → SpMat8Z :=
  ![SpMat8Z.one, gamma0Sp,
    mkSp2 gamma0Sp gamma1Sp, mkSp2 gamma0Sp gamma2Sp, mkSp2 gamma0Sp gamma3Sp,
    mkSp3 gamma1Sp gamma2Sp gamma3Sp,
    mkSp2 gamma1Sp p1Sp, mkSp2 gamma1Sp p2Sp, mkSp2 gamma1Sp p3Sp,
    mkSp2 gamma2Sp p1Sp, mkSp2 gamma2Sp p2Sp, mkSp2 gamma2Sp p3Sp,
    mkSp2 gamma3Sp p1Sp, mkSp2 gamma3Sp p2Sp, mkSp2 gamma3Sp p3Sp,
    mkSp3 gamma2Sp gamma3Sp p1Sp, mkSp3 gamma2Sp gamma3Sp p2Sp, mkSp3 gamma2Sp gamma3Sp p3Sp,
    mkSp3 gamma3Sp gamma1Sp p1Sp, mkSp3 gamma3Sp gamma1Sp p2Sp, mkSp3 gamma3Sp gamma1Sp p3Sp,
    mkSp3 gamma1Sp gamma2Sp p1Sp, mkSp3 gamma1Sp gamma2Sp p2Sp, mkSp3 gamma1Sp gamma2Sp p3Sp,
    mkSp4 gamma0Sp gamma2Sp gamma3Sp p1Sp, mkSp4 gamma0Sp gamma2Sp gamma3Sp p2Sp,
    mkSp4 gamma0Sp gamma2Sp gamma3Sp p3Sp,
    mkSp4 gamma0Sp gamma3Sp gamma1Sp p1Sp, mkSp4 gamma0Sp gamma3Sp gamma1Sp p2Sp,
    mkSp4 gamma0Sp gamma3Sp gamma1Sp p3Sp,
    mkSp4 gamma0Sp gamma1Sp gamma2Sp p1Sp, mkSp4 gamma0Sp gamma1Sp gamma2Sp p2Sp,
    mkSp4 gamma0Sp gamma1Sp gamma2Sp p3Sp,
    mkSp2 g0123Sp p1Sp, mkSp2 g0123Sp p2Sp, mkSp2 g0123Sp p3Sp]

/-- Daviau's 28 explicit skew-symmetric basis matrices over `ℤ` (p. 157):
`Γ₁, Γ₂, Γ₃, Γ₂₃, Γ₃₁, Γ₁₂, Γ₀₂₃, Γ₀₃₁, Γ₀₁₂, Γ₀₁₂₃`, and
`P_j, Γ₀P_j, Γ₀₁P_j, Γ₀₂P_j, Γ₀₃P_j, Γ₁₂₃P_j` (`j = 1,2,3`). -/
def skewBasis28Z : Fin 28 → Mat8Z :=
  ![gamma1Z, gamma2Z, gamma3Z,
    gamma2Z * gamma3Z, gamma3Z * gamma1Z, gamma1Z * gamma2Z,
    gamma0Z * gamma2Z * gamma3Z, gamma0Z * gamma3Z * gamma1Z, gamma0Z * gamma1Z * gamma2Z,
    gamma0123Z,
    p1Z, p2Z, p3Z,
    gamma0Z * p1Z, gamma0Z * p2Z, gamma0Z * p3Z,
    gamma0Z * gamma1Z * p1Z, gamma0Z * gamma1Z * p2Z, gamma0Z * gamma1Z * p3Z,
    gamma0Z * gamma2Z * p1Z, gamma0Z * gamma2Z * p2Z, gamma0Z * gamma2Z * p3Z,
    gamma0Z * gamma3Z * p1Z, gamma0Z * gamma3Z * p2Z, gamma0Z * gamma3Z * p3Z,
    gamma1Z * gamma2Z * gamma3Z * p1Z, gamma1Z * gamma2Z * gamma3Z * p2Z,
    gamma1Z * gamma2Z * gamma3Z * p3Z]

/-- Daviau's 36 explicit symmetric basis matrices over `ℤ` (p. 157):
`I₈, Γ₀, Γ₀₁, Γ₀₂, Γ₀₃, Γ₁₂₃`, and
`Γ₁P_j, Γ₂P_j, Γ₃P_j, Γ₂₃P_j, Γ₃₁P_j, Γ₁₂P_j, Γ₀₂₃P_j, Γ₀₃₁P_j, Γ₀₁₂P_j, Γ₀₁₂₃P_j` (`j = 1,2,3`). -/
def symBasis36Z : Fin 36 → Mat8Z :=
  ![1, gamma0Z,
    gamma0Z * gamma1Z, gamma0Z * gamma2Z, gamma0Z * gamma3Z,
    gamma1Z * gamma2Z * gamma3Z,
    gamma1Z * p1Z, gamma1Z * p2Z, gamma1Z * p3Z,
    gamma2Z * p1Z, gamma2Z * p2Z, gamma2Z * p3Z,
    gamma3Z * p1Z, gamma3Z * p2Z, gamma3Z * p3Z,
    gamma2Z * gamma3Z * p1Z, gamma2Z * gamma3Z * p2Z, gamma2Z * gamma3Z * p3Z,
    gamma3Z * gamma1Z * p1Z, gamma3Z * gamma1Z * p2Z, gamma3Z * gamma1Z * p3Z,
    gamma1Z * gamma2Z * p1Z, gamma1Z * gamma2Z * p2Z, gamma1Z * gamma2Z * p3Z,
    gamma0Z * gamma2Z * gamma3Z * p1Z, gamma0Z * gamma2Z * gamma3Z * p2Z,
    gamma0Z * gamma2Z * gamma3Z * p3Z,
    gamma0Z * gamma3Z * gamma1Z * p1Z, gamma0Z * gamma3Z * gamma1Z * p2Z,
    gamma0Z * gamma3Z * gamma1Z * p3Z,
    gamma0Z * gamma1Z * gamma2Z * p1Z, gamma0Z * gamma1Z * gamma2Z * p2Z,
    gamma0Z * gamma1Z * gamma2Z * p3Z,
    gamma0123Z * p1Z, gamma0123Z * p2Z, gamma0123Z * p3Z]

private theorem skewBasis28Z_eq_sp (k : Fin 28) :
    skewBasis28Z k = (skewBasis28Sp k).toMat := by
  fin_cases k <;>
    dsimp [skewBasis28Z, skewBasis28Sp, mkSp2, mkSp3, mkSp4] <;>
    simp [SpMat8Z.toMat_mul, gamma0Sp_toMat, gamma1Sp_toMat, gamma2Sp_toMat, gamma3Sp_toMat,
      p1Sp_toMat, p2Sp_toMat, p3Sp_toMat, g0123Sp_toMat]

private theorem symBasis36Z_eq_sp (k : Fin 36) :
    symBasis36Z k = (symBasis36Sp k).toMat := by
  fin_cases k <;>
    dsimp [symBasis36Z, symBasis36Sp, mkSp2, mkSp3, mkSp4] <;>
    simp [SpMat8Z.toMat_one, SpMat8Z.toMat_mul, gamma0Sp_toMat, gamma1Sp_toMat, gamma2Sp_toMat,
      gamma3Sp_toMat, p1Sp_toMat, p2Sp_toMat, p3Sp_toMat, g0123Sp_toMat]

def skewBasis28R (k : Fin 28) : Mat8R := castZ8 (skewBasis28Z k)
def symBasis36R (k : Fin 36) : Mat8R := castZ8 (symBasis36Z k)

/-- Explicit Frobenius inner product `trace (Aᵀ * B)` on `Mat8Z`. -/
def frobZ (A B : Mat8Z) : ℤ :=
  ∑ i : Fin 8, ∑ j : Fin 8, A i j * B i j

def spFrobZ (A B : SpMat8Z) : ℤ :=
  ∑ i : Fin 8, if A.col i = B.col i then A.sgn i * B.sgn i else 0

theorem frobZ_eq_trace_transpose_mul (A B : Mat8Z) :
    frobZ A B = Matrix.trace (Aᵀ * B) := by
  dsimp [frobZ, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem frobZ_toMat (A B : SpMat8Z) :
    frobZ A.toMat B.toMat = spFrobZ A B := by
  dsimp [frobZ, spFrobZ, SpMat8Z.toMat]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (A.col i)]
  · by_cases h : A.col i = B.col i <;> simp [h]
  · intro j _ hj; simp [hj]
  · intro hm; exact False.elim (hm (Finset.mem_univ _))

private theorem skewBasis28Sp_check (k : Fin 28) (i : Fin 8) :
    (skewBasis28Sp k).col ((skewBasis28Sp k).col i) = i ∧
    (skewBasis28Sp k).sgn ((skewBasis28Sp k).col i) = -(skewBasis28Sp k).sgn i ∧
    (skewBasis28Sp k).sgn i * (skewBasis28Sp k).sgn ((skewBasis28Sp k).col i) = -1 := by
  revert k i; decide

private theorem symBasis36Sp_check (k : Fin 36) (i : Fin 8) :
    (symBasis36Sp k).col ((symBasis36Sp k).col i) = i ∧
    (symBasis36Sp k).sgn ((symBasis36Sp k).col i) = (symBasis36Sp k).sgn i ∧
    (symBasis36Sp k).sgn i * (symBasis36Sp k).sgn ((symBasis36Sp k).col i) = 1 := by
  revert k i; decide

theorem skewBasis28Z_props (k : Fin 28) :
    (skewBasis28Z k)ᵀ = -skewBasis28Z k ∧ skewBasis28Z k * skewBasis28Z k = -(1 : Mat8Z) := by
  rw [skewBasis28Z_eq_sp k]
  have ht := (skewBasis28Sp k).toMat_transpose_of_inv (-1)
    (fun i => (skewBasis28Sp_check k i).1)
    (fun i => by rw [(skewBasis28Sp_check k i).2.1, neg_one_mul])
  have hs := (skewBasis28Sp k).toMat_sq_of_inv (-1)
    (fun i => (skewBasis28Sp_check k i).1)
    (fun i => (skewBasis28Sp_check k i).2.2)
  rw [neg_one_smul] at ht hs
  exact ⟨ht, hs⟩

theorem symBasis36Z_props (k : Fin 36) :
    (symBasis36Z k)ᵀ = symBasis36Z k ∧ symBasis36Z k * symBasis36Z k = (1 : Mat8Z) := by
  rw [symBasis36Z_eq_sp k]
  have ht := (symBasis36Sp k).toMat_transpose_of_inv 1
    (fun i => (symBasis36Sp_check k i).1)
    (fun i => by rw [(symBasis36Sp_check k i).2.1, one_mul])
  have hs := (symBasis36Sp k).toMat_sq_of_inv 1
    (fun i => (symBasis36Sp_check k i).1)
    (fun i => (symBasis36Sp_check k i).2.2)
  rw [one_smul] at ht hs
  exact ⟨ht, hs⟩

private theorem skewBasis28Sp_frob_ortho (a b : Fin 28) :
    spFrobZ (skewBasis28Sp a) (skewBasis28Sp b) = if a = b then 8 else 0 := by
  revert a b; decide

private theorem symBasis36Sp_frob_ortho (a b : Fin 36) :
    spFrobZ (symBasis36Sp a) (symBasis36Sp b) = if a = b then 8 else 0 := by
  revert a b; decide

theorem skewBasis28Z_frob_ortho (a b : Fin 28) :
    frobZ (skewBasis28Z a) (skewBasis28Z b) = if a = b then 8 else 0 := by
  rw [skewBasis28Z_eq_sp a, skewBasis28Z_eq_sp b, frobZ_toMat]
  exact skewBasis28Sp_frob_ortho a b

theorem symBasis36Z_frob_ortho (a b : Fin 36) :
    frobZ (symBasis36Z a) (symBasis36Z b) = if a = b then 8 else 0 := by
  rw [symBasis36Z_eq_sp a, symBasis36Z_eq_sp b, frobZ_toMat]
  exact symBasis36Sp_frob_ortho a b

private theorem trace_cast_frob (A B : Mat8Z) :
    Matrix.trace ((castZ8 A)ᵀ * castZ8 B) = (frobZ A B : ℝ) := by
  rw [frobZ_eq_trace_transpose_mul, ← castZ8_transpose, ← castZ8_mul, castZ8_trace]

/-- Linear independence from Frobenius trace orthogonality. -/
private theorem linearIndependent_of_frob_ortho {n : ℕ} (B : Fin n → Mat8Z)
    (hOrtho : ∀ a b : Fin n, frobZ (B a) (B b) = if a = b then 8 else 0) :
    LinearIndependent ℝ (fun k : Fin n => castZ8 (B k)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have htr : Matrix.trace ((castZ8 (B k))ᵀ * ∑ a : Fin n, c a • castZ8 (B a)) = 0 := by
    rw [hc, mul_zero, Matrix.trace_zero]
  rw [Matrix.mul_sum, Matrix.trace_sum] at htr
  have hterm : ∀ a : Fin n,
      Matrix.trace ((castZ8 (B k))ᵀ * (c a • castZ8 (B a))) =
        if a = k then c k * 8 else 0 := by
    intro a
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_cast_frob, hOrtho k a]
    by_cases hak : a = k
    · subst hak; simp
    · have hka : k ≠ a := Ne.symm hak
      simp [hak, hka]
  have hsum : (∑ a : Fin n, if a = k then c k * 8 else 0) = 0 := by
    calc
      (∑ a : Fin n, if a = k then c k * 8 else 0)
          = ∑ a : Fin n, Matrix.trace ((castZ8 (B k))ᵀ * (c a • castZ8 (B a))) :=
            Finset.sum_congr rfl fun a _ => (hterm a).symm
      _ = 0 := htr
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum
  exact (mul_eq_zero.mp hsum).resolve_right (by norm_num)

theorem skewBasis28R_mem_so8 (k : Fin 28) : skewBasis28R k ∈ so8Submodule := by
  change (castZ8 (skewBasis28Z k))ᵀ = -castZ8 (skewBasis28Z k)
  rw [← castZ8_transpose, (skewBasis28Z_props k).1, castZ8_neg]

theorem skewBasis28R_sq (k : Fin 28) : skewBasis28R k * skewBasis28R k = -(1 : Mat8R) := by
  dsimp [skewBasis28R]; rw [← castZ8_mul, (skewBasis28Z_props k).2, castZ8_neg, castZ8_one]

theorem symBasis36R_mem_sym8 (k : Fin 36) : symBasis36R k ∈ sym8Submodule := by
  change (castZ8 (symBasis36Z k))ᵀ = castZ8 (symBasis36Z k)
  rw [← castZ8_transpose, (symBasis36Z_props k).1]

theorem symBasis36R_sq (k : Fin 36) : symBasis36R k * symBasis36R k = (1 : Mat8R) := by
  dsimp [symBasis36R]; rw [← castZ8_mul, (symBasis36Z_props k).2, castZ8_one]

theorem skewBasis28R_linearIndependent : LinearIndependent ℝ skewBasis28R :=
  linearIndependent_of_frob_ortho skewBasis28Z skewBasis28Z_frob_ortho

theorem symBasis36R_linearIndependent : LinearIndependent ℝ symBasis36R :=
  linearIndependent_of_frob_ortho symBasis36Z symBasis36Z_frob_ortho

/-- Dimension count `64 = 28_{so(8)} + 36_{sym}` for `M₈(ℝ) = so(8) ⊕ sym(8)`. -/
theorem finrank_so8_sym8_split :
    Module.finrank ℝ Mat8R = 64 ∧
    Module.finrank ℝ so8Submodule = 28 ∧
    Module.finrank ℝ sym8Submodule = 36 := by
  have hMat : Module.finrank ℝ Mat8R = 64 := by
    rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self]
  have hle_so : 28 ≤ Module.finrank ℝ so8Submodule := by
    have hli : LinearIndependent ℝ (fun k : Fin 28 => (⟨skewBasis28R k, skewBasis28R_mem_so8 k⟩ : so8Submodule)) := by
      refine LinearIndependent.of_comp so8Submodule.subtype ?_
      exact skewBasis28R_linearIndependent
    simpa [Fintype.card_fin] using hli.fintype_card_le_finrank
  have hle_sym : 36 ≤ Module.finrank ℝ sym8Submodule := by
    have hli : LinearIndependent ℝ (fun k : Fin 36 => (⟨symBasis36R k, symBasis36R_mem_sym8 k⟩ : sym8Submodule)) := by
      refine LinearIndependent.of_comp sym8Submodule.subtype ?_
      exact symBasis36R_linearIndependent
    simpa [Fintype.card_fin] using hli.fintype_card_le_finrank
  have hadd : Module.finrank ℝ so8Submodule + Module.finrank ℝ sym8Submodule = Module.finrank ℝ Mat8R :=
    Submodule.finrank_add_eq_of_isCompl isCompl_so8_sym8
  omega

/-- **Theorem 1 (`daviau_realDirac_quatCommutant_so8_split`)**:
Real `8 × 8` Dirac matrices `{Γ^μ}` with `{Γ^μ, Γ^ν} = 2 g^{μν} I₈`, quaternionic commutant
`{P₁, P₂, P₃}` (Daviau Eq. 14), Krein metric `Γ⁰ = diag(I₄, -I₄)`, and `64 = 28_{so(8)} + 36_{sym}`. -/
theorem daviau_realDirac_quatCommutant_so8_split :
    (∀ μ ν : Fin 4, gammaR μ * gammaR ν + gammaR ν * gammaR μ =
      (if μ = ν then 2 * minkowskiMetricR μ else 0) • (1 : Mat8R)) ∧
    (∀ (μ : Fin 4) (j : Fin 3), gammaR μ * quatPR j = quatPR j * gammaR μ) ∧
    (∀ j : Fin 3, quatPR j * quatPR j = -(1 : Mat8R)) ∧
    (quatPR 0 * quatPR 1 = quatPR 2 ∧ quatPR 1 * quatPR 0 = -quatPR 2 ∧
     quatPR 1 * quatPR 2 = quatPR 0 ∧ quatPR 2 * quatPR 1 = -quatPR 0 ∧
     quatPR 2 * quatPR 0 = quatPR 1 ∧ quatPR 0 * quatPR 2 = -quatPR 1) ∧
    gammaR 0 = InfoGeometry.Canonical.KreinMajoranaBlockInvariance.kreinMetric8 ∧
    (∀ μ : Fin 4, (gammaR μ)ᵀ * gammaR 0 = gammaR 0 * gammaR μ) ∧
    IsCompl so8Submodule sym8Submodule ∧
    Module.finrank ℝ Mat8R = 64 ∧
    Module.finrank ℝ so8Submodule = 28 ∧
    Module.finrank ℝ sym8Submodule = 36 ∧
    (∀ k : Fin 28, skewBasis28R k ∈ so8Submodule ∧ skewBasis28R k * skewBasis28R k = -(1 : Mat8R)) ∧
    (∀ k : Fin 36, symBasis36R k ∈ sym8Submodule ∧ symBasis36R k * symBasis36R k = (1 : Mat8R)) :=
  ⟨gammaR_anticomm,
   gammaR_comm_quatPR,
   quatPR_sq,
   ⟨quatPR_01, quatPR_10, quatPR_12, quatPR_21, quatPR_20, quatPR_02⟩,
   gamma0R_eq_kreinMetric8,
   gammaR_krein_adjoint,
   isCompl_so8_sym8,
   finrank_so8_sym8_split.1,
   finrank_so8_sym8_split.2.1,
   finrank_so8_sym8_split.2.2,
   fun k => ⟨skewBasis28R_mem_so8 k, skewBasis28R_sq k⟩,
   fun k => ⟨symBasis36R_mem_sym8 k, symBasis36R_sq k⟩⟩

end InfoGeometry.Clifford.DaviauRealDirac8x8
