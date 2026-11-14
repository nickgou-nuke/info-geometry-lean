/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeFutureHorizonsTower

/-!
# Noncommutative Historical Comparison & Contrast Archetypes (`CM₁`–`CM₅`)

Formalizes over arbitrary noncommutative rings `[Ring B]`, `[Ring A] [StarRing A]`,
and `NestedMat ℤ` (`M₂(M₂(ℤ))`) the five decisive contrast theorems (`CM₁`–`CM₅`)
separating commutative/central/orthogonal collapses from noncommutative operator
constructions:
1. `CM₁`: Central braiding collapse `twistedCocycle X Q n = Q ^ n` vs. non-central
   Witt-link monodromy (`X_blk² = Z_blk² = 1`, `W^(2) = 1`, `Q_blk^n = 1 + n • N_blk ≠ 1`).
2. `CM₂`: Commuting projection triviality `symCompress P Q - (symCompress P Q)² = 0`
   vs. noncommutative Cayley–Peirce FUP variance `2 • T_fup - T_fup² = P_plus`.
3. `CM₃` & `CM₄`: Constant Abelian curvature collapse `mcCurvature 0 0 A₁ A₂ = 0`
   and scalar Casimir collapse vs. quaternion braid curvature `2 • E₃` and
   `sl₂` Lie cross-product obstruction.
4. `CM₅`: Córdova–Freed–Teleman dichotomy in `M₂(M₂(ℤ))`: orthogonal gapped boundary
   generators `T1_orth, T2_orth` with finite torsion anomaly `A_torsion^4 = 1` vs.
   non-orthogonal unipotent Witt shift `X_blk` generating infinite-order `Q_blk`.
-/

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeHistoricalComparisonSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

/-- Explicit `2 × 2` matrix constructor avoiding `vecCons`/`vecMul` simp expansion. -/
def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  fun i j => match i, j with
  | 0, 0 => a
  | 0, 1 => b
  | 1, 0 => c
  | 1, 1 => d

lemma ext_fin2 {A : Type*} {M N : Matrix (Fin 2) (Fin 2) A}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  ext i j; fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

section Matrix2Simp

variable {A : Type*} [Ring A]

omit [Ring A] in @[simp] lemma mat2_00 (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
omit [Ring A] in @[simp] lemma mat2_01 (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
omit [Ring A] in @[simp] lemma mat2_10 (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
omit [Ring A] in @[simp] lemma mat2_11 (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma mul2_00 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_01 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_10 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by rw [Matrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma mul2_11 (M N : Matrix (Fin 2) (Fin 2) A) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by rw [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma one2_00 : (1 : Matrix (Fin 2) (Fin 2) A) 0 0 = 1 := rfl
@[simp] lemma one2_01 : (1 : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
@[simp] lemma one2_10 : (1 : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
@[simp] lemma one2_11 : (1 : Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl

omit [Ring A] in @[simp] lemma tr2_00 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 0 = M 0 0 := rfl
omit [Ring A] in @[simp] lemma tr2_01 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 1 = M 1 0 := rfl
omit [Ring A] in @[simp] lemma tr2_10 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 0 = M 0 1 := rfl
omit [Ring A] in @[simp] lemma tr2_11 (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 1 = M 1 1 := rfl

omit [Ring A] in @[simp] lemma ct2_00 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 0 = star (M 0 0) := rfl
omit [Ring A] in @[simp] lemma ct2_01 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 0 1 = star (M 1 0) := rfl
omit [Ring A] in @[simp] lemma ct2_10 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 0 = star (M 0 1) := rfl
omit [Ring A] in @[simp] lemma ct2_11 [Star A] (M : Matrix (Fin 2) (Fin 2) A) :
    Mᴴ 1 1 = star (M 1 1) := rfl

def gamma1Op   : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 (-1)
def sigmaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 1 1 0
def omegaOp    : Matrix (Fin 2) (Fin 2) A := mat2 0 (-1) 1 0
def P_plus     : Matrix (Fin 2) (Fin 2) A := mat2 1 0 0 0
def F_plus     : Matrix (Fin 2) (Fin 2) A := mat2 0 1 0 0
def F_minus    : Matrix (Fin 2) (Fin 2) A := mat2 0 0 1 0
def N_plus     : Matrix (Fin 2) (Fin 2) A := mat2 (-1) (-1) 1 1
def fiberEmbed (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 a
def kleinTwist (a : A) : Matrix (Fin 2) (Fin 2) A := mat2 a 0 0 (-a)

end Matrix2Simp

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

/-!
## Contrast CM₁: Central Braiding Collapse vs. Non-Central Infinite-Order Parabolic Monodromy
-/

section ContrastCM1_CentralVsParabolicCocycle

def conjBy {G : Type*} [Group G] (x q : G) : G := x * q * x⁻¹

def twistedCocycle {G : Type*} [Group G] (X Q : G) : ℕ → G
  | 0     => 1
  | n + 1 => Q * conjBy X (twistedCocycle X Q n)

/-- When `Q` commutes with `X`, the Wilson 1-cocycle `twistedCocycle X Q n` collapses to `Q ^ n`. -/
theorem central_cocycle_collapses_to_pow {G : Type*} [Group G] {X Q : G}
    (h_comm : X * Q = Q * X) (n : ℕ) :
    twistedCocycle X Q n = Q ^ n := by
  have h_conj : ∀ k : ℕ, X * Q ^ k * X⁻¹ = Q ^ k := by
    intro k
    induction' k with k ih
    · group
    · calc X * Q ^ (k + 1) * X⁻¹
        _ = (X * Q * X⁻¹) * (X * Q ^ k * X⁻¹) := by rw [pow_succ']; group
        _ = Q * Q ^ k := by rw [ih, h_comm]; group
        _ = Q ^ (k + 1) := by rw [← pow_succ']
  induction' n with n ih
  · simp [twistedCocycle]
  · rw [twistedCocycle, ih, conjBy, h_conj n, ← pow_succ']

def X_blk {B : Type*} [Ring B] : NestedMat B := mat2 0 (1 - F_plus) (1 + F_plus) 0
def Z_blk {B : Type*} [Ring B] : NestedMat B := mat2 sigmaOp 0 0 gamma1Op
def N_blk {B : Type*} [Ring B] : NestedMat B := mat2 N_plus 0 0 (-F_minus)
def Q_blk {B : Type*} [Ring B] : NestedMat B := (Z_blk * X_blk) * (Z_blk * X_blk)

/-- Additive readout of the lower-left coefficient in the upper-left operator block. -/
def nestedCornerEntry {B : Type*} [Ring B] : NestedMat B →+ B where
  toFun M := M 0 0 1 0
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Contrast Theorem `CM₁`**:
Whereas any central braiding phase `Q` collapses `twistedCocycle X Q n = Q ^ n`, the non-central
Witt-link operators `X_blk, Z_blk ∈ M₂(M₂(B))` satisfy `X_blk² = Z_blk² = 1` and
`Q_blk * (X_blk * Q_blk * X_blk) = 1`, while `Q_blk ^ n = 1 + n • N_blk` has infinite order
over any `[CharZero B]`. -/
theorem contrast_central_collapse_vs_noncentral_parabolic_monodromy
    {B : Type*} [Ring B] [CharZero B] (n : ℕ) (hn : 0 < n) :
    (X_blk : NestedMat B) * X_blk = 1 ∧
    (Z_blk : NestedMat B) * Z_blk = 1 ∧
    (Q_blk : NestedMat B) * (X_blk * Q_blk * X_blk) = 1 ∧
    (Q_blk : NestedMat B) ^ n = 1 + n • N_blk ∧
    (Q_blk : NestedMat B) ^ n ≠ 1 := by
  have hQ : (Q_blk : NestedMat B) = 1 + N_blk := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, sigmaOp, gamma1Op, F_plus, F_minus, N_blk, N_plus]
  have hN2 : (N_blk : NestedMat B) * N_blk = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [N_blk, N_plus, F_minus]
  have hPow : ∀ k : ℕ, (Q_blk : NestedMat B) ^ k = 1 + k • N_blk := by
    intro k
    induction' k with k ih
    · simp
    · rw [pow_succ, ih, hQ, add_nsmul, one_nsmul]
      have h_mul : (k • (N_blk : NestedMat B)) * N_blk = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hN2, mul_zero]
      calc (1 + k • (N_blk : NestedMat B)) * (1 + N_blk)
        _ = 1 + (k • N_blk + N_blk) + (k • N_blk) * N_blk := by noncomm_ring
        _ = 1 + (k • N_blk + N_blk) := by rw [h_mul, add_zero]
  refine ⟨?_, ?_, ?_, hPow n, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [X_blk, F_plus]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [Z_blk, sigmaOp, gamma1Op]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, sigmaOp, gamma1Op, F_plus]
  · intro h_eq
    rw [hPow n] at h_eq
    have h_nsmul : n • (N_blk : NestedMat B) = 0 := by
      exact add_left_cancel (show (1 : NestedMat B) + n • N_blk = 1 + 0 by simpa using h_eq)
    have h_zero : (n : B) = 0 := by
      have h_readout := congrArg (fun M : NestedMat B => (M 0 0) 1 0) h_nsmul
      simpa [N_blk, N_plus, mat2] using h_readout
    exact Nat.ne_of_gt hn (Nat.cast_eq_zero.mp h_zero)

end ContrastCM1_CentralVsParabolicCocycle

/-!
## Contrast CM₂: Commuting Projection Triviality vs. Noncommutative Cayley–Peirce FUP Variance
-/

section ContrastCM2_CommutingVsNoncommutingFUPVariance

variable {A : Type*} [Ring A] [StarRing A]

def symCompress {B : Type*} [Ring B] (P Q : B) : B := P * Q * P
def cayleyOp : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp

/-- Commuting idempotents have an idempotent compression in any associative ring. -/
theorem commuting_idempotent_compression_idempotent {B : Type*} [Ring B]
    {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q) (h_comm : ⁅P, Q⁆ = 0) :
    symCompress P Q * symCompress P Q = symCompress P Q := by
  have hPQ : P * Q = Q * P := sub_eq_zero.mp (by rw [← Ring.lie_def, h_comm])
  dsimp [symCompress]
  calc P * Q * P * (P * Q * P)
      = P * Q * (P * P) * Q * P := by noncomm_ring
    _ = P * Q * P * Q * P := by rw [hP]
    _ = P * (Q * P) * Q * P := by noncomm_ring
    _ = P * (P * Q) * Q * P := by rw [hPQ]
    _ = (P * P) * (Q * Q) * P := by noncomm_ring
    _ = P * Q * P := by rw [hP, hQ]

/-- **Contrast Theorem `CM₂`**:
1. Whenever `P, Q ∈ B` commute (`⁅P, Q⁆ = 0`), `symCompress P Q - symCompress P Q * symCompress P Q = 0`.
2. For `P_plus` and `Q_dual = cayleyOp * P_plus * cayleyOpᴴ`, `⁅P_plus, Q_dual⁆ = -omegaOp`
   and `2 • T_fup - T_fup * T_fup = P_plus`. -/
theorem contrast_commuting_projection_vs_cayley_peirce_fup_variance
    {B : Type*} [Ring B] {P Q : B} (hP : P * P = P) (hQ : Q * Q = Q) (h_comm : ⁅P, Q⁆ = 0) :
    let Q_dual : Matrix (Fin 2) (Fin 2) A := cayleyOp * P_plus * cayleyOpᴴ
    let T_fup  : Matrix (Fin 2) (Fin 2) A := symCompress P_plus Q_dual
    symCompress P Q - symCompress P Q * symCompress P Q = 0 ∧
    ⁅(P_plus : Matrix (Fin 2) (Fin 2) A), Q_dual⁆ = -omegaOp ∧
    2 • T_fup - T_fup * T_fup = (P_plus : Matrix (Fin 2) (Fin 2) A) := by
  have hPQ : P * Q = Q * P := sub_eq_zero.mp (by rw [← Ring.lie_def, h_comm])
  refine ⟨?_, ?_, ?_⟩
  · have h_idem := commuting_idempotent_compression_idempotent hP hQ h_comm
    rw [h_idem]
    exact sub_self _
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [cayleyOp, P_plus, omegaOp]
  · apply ext_fin2 <;> simp [symCompress, cayleyOp, P_plus, omegaOp, two_smul]

end ContrastCM2_CommutingVsNoncommutingFUPVariance

/-!
## Contrast CM₃ & CM₄: Constant Abelian Curvature & Commutative Cayley–Hamilton Collapse vs. Noncommutative Obstructions
-/

section ContrastCM3_CM4_CurvatureAndCharpolyObstructions

variable {A : Type*} [Ring A]

def mcCurvature {B : Type*} [Ring B] (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B :=
  d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆

def flowGen (cGamma cSigma cOmega : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed cGamma * gamma1Op + fiberEmbed cSigma * sigmaOp + fiberEmbed cOmega * omegaOp

def E₁ : NestedMat A := omegaOp
def E₂ : NestedMat A := kleinTwist omegaOp
def E₃ : NestedMat A := (E₁ : NestedMat A) * E₂

/-- **Contrast Theorem `CM₃` & `CM₄`**:
1. For commuting connections `⁅A₁, A₂⁆ = 0`, `mcCurvature 0 0 A₁ A₂ = 0`, whereas for
   the Brauer–Weyl quaternion potentials `E₁, E₂ ∈ M₂(M₂(A))`, `mcCurvature 0 0 E₁ E₂ = 2 • E₃`.
2. In `M₂(A)`, `flowGen cGamma cSigma cOmega ^ 2` differs from `fiberEmbed (cGamma^2 + cSigma^2 - cOmega^2)`
   by the exact non-Abelian `sl₂` Lie cross product. -/
theorem contrast_abelian_collapse_vs_noncommutative_curvature_and_charpoly
    {A₁ A₂ : A} (hA_comm : ⁅A₁, A₂⁆ = 0) (cGamma cSigma cOmega : A) :
    mcCurvature (0 : A →+ A) 0 A₁ A₂ = 0 ∧
    mcCurvature (0 : NestedMat A →+ NestedMat A) 0 (E₁ : NestedMat A) E₂ = 2 • E₃ ∧
    flowGen cGamma cSigma cOmega * flowGen cGamma cSigma cOmega -
      fiberEmbed (cGamma * cGamma + cSigma * cSigma - cOmega * cOmega) * 1 =
      fiberEmbed ⁅cSigma, cOmega⁆ * gamma1Op +
      fiberEmbed ⁅cOmega, cGamma⁆ * sigmaOp -
      fiberEmbed ⁅cGamma, cSigma⁆ * omegaOp := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [mcCurvature]; simp [hA_comm]
  · dsimp [mcCurvature]; rw [Ring.lie_def]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [E₁, E₂, E₃, kleinTwist, omegaOp, two_smul]
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp] <;> noncomm_ring

end ContrastCM3_CM4_CurvatureAndCharpolyObstructions

/-!
## Contrast CM₅: The Córdova–Freed–Teleman Dichotomy — Orthogonal Gapped Torsion vs. Non-Orthogonal Parabolic Monodromy
-/

section ContrastCM5_OrthogonalTorsionVsNonOrthogonalParabolic

def T1_orth   : NestedMat ℤ := sigmaOp
def T2_orth   : NestedMat ℤ := mat2 omegaOp 0 0 1
def A_torsion : NestedMat ℤ := mat2 (-omegaOp) 0 0 omegaOp

/-- **Contrast Theorem `CM₅` (The Gapped-Torsion vs. Gapless-Parabolic Dichotomy)**:
In `M₂(M₂(ℤ))`:
1. The gapped boundary generators `T1_orth, T2_orth` are orthogonal (`T1ᵀ * T1 = 1`, `T2ᵀ * T2 = 1`)
   and satisfy `T1_orth * T2_orth = A_torsion * T2_orth * T1_orth`, where `A_torsion` has
   finite torsion order 4 (`A_torsion ^ 2 ≠ 1`, `A_torsion ^ 4 = 1`).
2. The unipotent Witt-link shift `X_blk` violates orthogonality (`X_blkᵀ * X_blk ≠ 1`), allowing
   `Q_blk` to attain infinite multiplicative order (`Q_blk ^ n ≠ 1` for all `n > 0`). -/
theorem contrast_orthogonal_gapped_torsion_vs_nonorthogonal_parabolic
    (n : ℕ) (hn : 0 < n) :
    (T1_orth : NestedMat ℤ)ᴴ * T1_orth = 1 ∧
    (T2_orth : NestedMat ℤ)ᴴ * T2_orth = 1 ∧
    T1_orth * T2_orth = A_torsion * T2_orth * T1_orth ∧
    (A_torsion : NestedMat ℤ) ^ 2 ≠ 1 ∧
    (A_torsion : NestedMat ℤ) ^ 4 = 1 ∧
    (X_blk : NestedMat ℤ)ᴴ * X_blk ≠ 1 ∧
    (Q_blk : NestedMat ℤ) ^ n ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [T1_orth, sigmaOp]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [T2_orth, omegaOp]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [T1_orth, T2_orth, A_torsion, sigmaOp, omegaOp]
  · exact (by decide : (A_torsion : NestedMat ℤ) ^ 2 ≠ 1)
  · rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
    apply ext_fin2 <;> apply ext_fin2 <;> simp [A_torsion, omegaOp, sq]
  · exact (by decide : (X_blk : NestedMat ℤ)ᴴ * X_blk ≠ 1)
  · exact (contrast_central_collapse_vs_noncentral_parabolic_monodromy n hn).2.2.2.2

end ContrastCM5_OrthogonalTorsionVsNonOrthogonalParabolic


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeHistoricalComparisonSynthesis
