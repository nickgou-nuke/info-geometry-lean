/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealChiralDiracSolderingBridge
import InfoGeometry.Bridge.OperatorPauliLubanskiLift
import InfoGeometry.Canonical.PauliWeylTwistorQuarkColorBridge
import InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge
import InfoGeometry.Canonical.KleinianZornCl44Bridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Unified Polarized Spin Algebras, Finite Lorentz Covariance on `weylDirac8`, & `Cl(4,4)` Zorn Color Split

Completes the kinematic-to-dynamical chain uniting `RealChiralDiracSolderingBridge.weylDirac8`
inside `M₈(ℝ) = M₂(M₄(ℝ))` (zero complex `i`) with the polarized chiral spin algebras,
finite Lorentz boost/rotation rotors, rest-frame Pauli–Lubanski spin Casimir, and the
signature-`(4,4)` (`M₁₆(ℝ)`) Zorn `1 + 3 + 3 + 1` lepton–quark color decomposition:

1. **Part 1 — Unified `so(3,1)` & Polarized Chiral `su(2) ⊕ su(2)` Spin Algebras**:
   Constructs spatial Pauli generators `sigma4_a = realSoldering4 0 e_a`, rotation generators
   `rot4_a = (1/2) fiberJ4 sigma4_a`, 8D Lorentz generators `lorJ8` / `lorK8`, and polarized
   chiral spin algebras `spinPlus8 = P₊ ⊗ S_a` and `spinMinus8 = P₋ ⊗ S_a` acting directly
   on `weylDirac8` and exchanged by `mirror8 = X ⊗ I₄`.
2. **Part 2 — Lorentz Equivariance, Massive Factorization, & Pauli–Lubanski Spin Casimir**:
   Proves `[J_a, D(x)]` and `[K_a, D(x)]` for all `a ∈ {1,2,3}`, massive factorization
   `(D(p) - m I₈)(D(p) + m I₈) = (p² - m²) I₈`, rest-frame lock `D(m,0,0,0) = m mirror8`,
   and the `s = 1/2` Pauli–Lubanski Casimir `W² = (-3/4 m²) I₈` matched to
   `OperatorPauliLubanskiLift.rest_frame_massive_casimir`.
3. **Part 3 — Finite Spinor Lorentz Boosts & Spatial Rotations (`SL(2,ℂ)_ℝ ⊂ M₈(ℝ)`)**:
   Constructs `boostRotor8_1`, `boostRotor8_3`, `rotRotor8_1`, proves the exact group laws,
   inverses, finite boost/rotation covariance of `weylDirac8`, and lifts
   `lorentzBoost2_eq_cosh_add_sinh_xMir2` / `transferMatHyp_half_eq_cosh_add_sinh_xMir2` into `M₈(ℝ)`.
4. **Part 4 — `k = 2 → k = 3` (`M₁₆(ℝ)`) Lift & Zorn `1 + 3 + 3 + 1` Color Split Capstone**:
   Embeds `weylDirac8` into `M₁₆(ℝ)` alongside `SplitOctonion1331OperatorGradingBridge`,
   `PauliWeylTwistorQuarkColor`, and `KleinianZornCl44Bridge`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & ANALYTIC THEOREMS
* `exists_noncomm_mat4_pol`, `exists_noncomm_mat2x4_pol`, `exists_noncomm_mat2x8_pol`
* `polarized_spin_algebras_on_weylDirac8`
* `weylDirac8_lorentz_equivariance_and_massive_casimir`
* `finite_lorentz_boost_and_rotation_covariance_weylDirac8`
* `weylDirac8_zorn_cl44_lepton_quark_color_capstone`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* Nullity/rank-4 Kleinian kernel statements in the Zorn `Cl(4,4)` capstone under explicit
  nonzero null element hypotheses (`hz : z ≠ 0`, `hnull : zornNormFun z = 0`).

#### BUCKET 3: OPEN CLOSURE DEBT
* Dynamic continuum interacting `SU(3)` gauge-boson quantum Yang–Mills mass gap and curved
  spinor bundle transitions remain outside this finite-matrix algebraic and rotor bridge.
-/

noncomputable section

open scoped BigOperators Kronecker
open Matrix
open InfoGeometry.Canonical.RealChiralDiracSolderingBridge

namespace InfoGeometry.Canonical.PolarizedWeylDiracLorentzColorBridge

/-! ### Part 1: Polarized `so(3,1)` & Two Commuting Chiral `su(2)` Spin Algebras on `weylDirac8` -/

/-- Realified spatial Pauli generators `Σ₁, Σ₂, Σ₃ ∈ M₄(ℝ)`. -/
def sigma4_1 : Matrix (Fin 4) (Fin 4) ℝ := realSoldering4 0 1 0 0
def sigma4_2 : Matrix (Fin 4) (Fin 4) ℝ := realSoldering4 0 0 1 0
def sigma4_3 : Matrix (Fin 4) (Fin 4) ℝ := realSoldering4 0 0 0 1

/-- Realified `su(2)` spin rotation generators `S_a = ½ fiberJ4 * Σ_a ∈ M₄(ℝ)`. -/
def rot4_1 : Matrix (Fin 4) (Fin 4) ℝ := (1 / 2 : ℝ) • (fiberJ4 * sigma4_1)
def rot4_2 : Matrix (Fin 4) (Fin 4) ℝ := (1 / 2 : ℝ) • (fiberJ4 * sigma4_2)
def rot4_3 : Matrix (Fin 4) (Fin 4) ℝ := (1 / 2 : ℝ) • (fiberJ4 * sigma4_3)

/-- 8D rotation generators `𝒥_a = I₂ ⊗ S_a ∈ M₂(M₄(ℝ))`. -/
def lorJ8 (S : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ S

/-- 8D boost generators `𝒦_a = ½ Z ⊗ Σ_a ∈ M₂(M₄(ℝ))`. -/
def lorK8 (K : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  (1 / 2 : ℝ) • (zCut2 ⊗ₖ K)

/-- Polarized positive-chirality spin generator `S⁺ = ½(𝒥 + J₈ 𝒦) = P₊ ⊗ S`. -/
def spinPlus8 (S K : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  (1 / 2 : ℝ) • (lorJ8 S + fiberJ8 * lorK8 K)

/-- Polarized negative-chirality spin generator `S⁻ = ½(𝒥 - J₈ 𝒦) = P₋ ⊗ S`. -/
def spinMinus8 (S K : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  (1 / 2 : ℝ) • (lorJ8 S - fiberJ8 * lorK8 K)

private lemma kronecker_sub_left {l m n p : Type*} (A B : Matrix l m ℝ) (C : Matrix n p ℝ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, sub_mul]

private lemma kronecker_sub_right {l m n p : Type*} (A : Matrix l m ℝ) (B C : Matrix n p ℝ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, mul_sub]

private lemma neg_kronecker24_pol (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kronecker_neg24_pol (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma rot4_1_2 : rot4_1 * rot4_2 - rot4_2 * rot4_1 = rot4_3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_1, rot4_2, rot4_3, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;>
    norm_num

private lemma rot4_2_3 : rot4_2 * rot4_3 - rot4_3 * rot4_2 = rot4_1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_1, rot4_2, rot4_3, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;>
    norm_num

private lemma rot4_3_1 : rot4_3 * rot4_1 - rot4_1 * rot4_3 = rot4_2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_1, rot4_2, rot4_3, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;>
    norm_num

private lemma sigma4_1_2 : sigma4_1 * sigma4_2 - sigma4_2 * sigma4_1 = -((4 : ℝ) • rot4_3) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_3, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;> norm_num

private lemma sigma4_2_3 : sigma4_2 * sigma4_3 - sigma4_3 * sigma4_2 = -((4 : ℝ) • rot4_1) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_1, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;> norm_num

private lemma sigma4_3_1 : sigma4_3 * sigma4_1 - sigma4_1 * sigma4_3 = -((4 : ℝ) • rot4_2) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_2, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;> norm_num

private lemma rot4_1_sigma2 : rot4_1 * sigma4_2 - sigma4_2 * rot4_1 = sigma4_3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_1, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;> norm_num

private lemma rot4_2_sigma3 : rot4_2 * sigma4_3 - sigma4_3 * rot4_2 = sigma4_1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_2, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;> norm_num

private lemma rot4_3_sigma1 : rot4_3 * sigma4_1 - sigma4_1 * rot4_3 = sigma4_2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_3, fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4] <;> norm_num

private lemma rot4_1_sq : rot4_1 * rot4_1 = (-1 / 4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_1, fiberJ4, sigma4_1, realSoldering4] <;> norm_num

private lemma rot4_2_sq : rot4_2 * rot4_2 = (-1 / 4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_2, fiberJ4, sigma4_2, realSoldering4] <;> norm_num

private lemma rot4_3_sq : rot4_3 * rot4_3 = (-1 / 4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_3, fiberJ4, sigma4_3, realSoldering4] <;> norm_num

/-- Explicit non-commutativity witness in `Matrix (Fin 4) (Fin 4) ℝ`. -/
theorem exists_noncomm_mat4_pol :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨rot4_1, rot4_2, fun h => ?_⟩
  have hDiff : rot4_3 = 0 := by rw [← rot4_1_2, h, sub_self]
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) hDiff
  simp [rot4_3, fiberJ4, sigma4_3, realSoldering4] at h01

/-- Explicit non-commutativity witness in `Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ`. -/
theorem exists_noncomm_mat2x4_pol :
    ∃ A B : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ, A * B ≠ B * A := by
  refine ⟨lorJ8 rot4_1, lorJ8 rot4_2, fun h => ?_⟩
  have hJ3 : lorJ8 rot4_3 = 0 := by
    calc lorJ8 rot4_3 = (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (rot4_1 * rot4_2 - rot4_2 * rot4_1) := by
            rw [rot4_1_2]; rfl
      _ = lorJ8 rot4_1 * lorJ8 rot4_2 - lorJ8 rot4_2 * lorJ8 rot4_1 := by
            simp only [lorJ8, kronecker_sub_right, ← Matrix.mul_kronecker_mul, one_mul]
      _ = 0 := sub_eq_zero.mpr h
  have h01 := congrArg
    (fun M : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ => M (0, 0) (0, 1)) hJ3
  simp [lorJ8, rot4_3, fiberJ4, sigma4_3, realSoldering4] at h01

private lemma sigma4_mul_self :
    sigma4_1 * sigma4_1 = 1 ∧ sigma4_2 * sigma4_2 = 1 ∧ sigma4_3 * sigma4_3 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [sigma4_1, sigma4_2, sigma4_3, realSoldering4,
          Matrix.mul_apply, Fin.sum_univ_four] }

private lemma sigma4_comm_fiberJ4 :
    fiberJ4 * sigma4_1 = sigma4_1 * fiberJ4 ∧
    fiberJ4 * sigma4_2 = sigma4_2 * fiberJ4 ∧
    fiberJ4 * sigma4_3 = sigma4_3 * fiberJ4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [fiberJ4, sigma4_1, sigma4_2, sigma4_3, realSoldering4,
          Matrix.mul_apply, Fin.sum_univ_four] }

private lemma fiberJ4_sq : fiberJ4 * fiberJ4 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [fiberJ4, Matrix.mul_apply, Fin.sum_univ_four]

private lemma rot4_brackets :
    (rot4_1 * rot4_2 - rot4_2 * rot4_1 = rot4_3) ∧
    (rot4_2 * rot4_3 - rot4_3 * rot4_2 = rot4_1) ∧
    (rot4_3 * rot4_1 - rot4_1 * rot4_3 = rot4_2) ∧
    (sigma4_1 * sigma4_2 - sigma4_2 * sigma4_1 = -((4 : ℝ) • rot4_3)) ∧
    (sigma4_2 * sigma4_3 - sigma4_3 * sigma4_2 = -((4 : ℝ) • rot4_1)) ∧
    (sigma4_3 * sigma4_1 - sigma4_1 * sigma4_3 = -((4 : ℝ) • rot4_2)) ∧
    (rot4_1 * sigma4_2 - sigma4_2 * rot4_1 = sigma4_3) ∧
    (rot4_2 * sigma4_3 - sigma4_3 * rot4_2 = sigma4_1) ∧
    (rot4_3 * sigma4_1 - sigma4_1 * rot4_3 = sigma4_2) :=
  ⟨rot4_1_2, rot4_2_3, rot4_3_1, sigma4_1_2, sigma4_2_3, sigma4_3_1,
    rot4_1_sigma2, rot4_2_sigma3, rot4_3_sigma1⟩

private lemma rot4_casimir_sq :
    rot4_1 * rot4_1 + rot4_2 * rot4_2 + rot4_3 * rot4_3 = (-3 / 4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  rw [rot4_1_sq, rot4_2_sq, rot4_3_sq, ← add_smul, ← add_smul]
  norm_num

private lemma two_smul_rot4 (K : Matrix (Fin 4) (Fin 4) ℝ) :
    (1 / 2 : ℝ) • ((2 : ℝ) • ((1 / 2 : ℝ) • (fiberJ4 * K))) = (1 / 2 : ℝ) • (fiberJ4 * K) := by
  rw [smul_smul, smul_smul]; norm_num

private lemma pPlus2_half_zCut : (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + zCut2) = pPlus2 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [zCut2, pPlus2, pMinus2]; try norm_num)

private lemma pMinus2_half_zCut : (1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) - zCut2) = pMinus2 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [zCut2, pPlus2, pMinus2]; try norm_num)

private lemma spinPlus8_eq_kron (S K : Matrix (Fin 4) (Fin 4) ℝ) (hFS : fiberJ4 * K = (2 : ℝ) • S) :
    spinPlus8 S K = pPlus2 ⊗ₖ S := by
  dsimp [spinPlus8, fiberJ8, lorJ8, lorK8]
  rw [mul_smul_comm, ← Matrix.mul_kronecker_mul, one_mul, hFS, Matrix.kronecker_smul, smul_smul]
  have hHalfTwo : ((1 / 2 : ℝ) * 2) = 1 := by norm_num
  rw [hHalfTwo, one_smul, ← Matrix.add_kronecker, ← Matrix.smul_kronecker, pPlus2_half_zCut]

private lemma spinMinus8_eq_kron (S K : Matrix (Fin 4) (Fin 4) ℝ) (hFS : fiberJ4 * K = (2 : ℝ) • S) :
    spinMinus8 S K = pMinus2 ⊗ₖ S := by
  dsimp [spinMinus8, fiberJ8, lorJ8, lorK8]
  rw [mul_smul_comm, ← Matrix.mul_kronecker_mul, one_mul, hFS, Matrix.kronecker_smul, smul_smul]
  have hHalfTwo : ((1 / 2 : ℝ) * 2) = 1 := by norm_num
  rw [hHalfTwo, one_smul, ← kronecker_sub_left, ← Matrix.smul_kronecker, pMinus2_half_zCut]

private lemma fiberJ4_rot4_1_comm : fiberJ4 * rot4_1 = rot4_1 * fiberJ4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [fiberJ4, rot4_1, sigma4_1, realSoldering4]

private lemma rot4_sigma_prod_half :
    (1 / 2 : ℝ) • (rot4_1 * sigma4_1) + (1 / 2 : ℝ) • (rot4_2 * sigma4_2) +
      (1 / 2 : ℝ) • (rot4_3 * sigma4_3) = (3 / 4 : ℝ) • fiberJ4 := by
  have h1 : rot4_1 * sigma4_1 = (1 / 2 : ℝ) • fiberJ4 := by
    dsimp [rot4_1]; rw [smul_mul_assoc, Matrix.mul_assoc, sigma4_mul_self.1, mul_one]
  have h2 : rot4_2 * sigma4_2 = (1 / 2 : ℝ) • fiberJ4 := by
    dsimp [rot4_2]; rw [smul_mul_assoc, Matrix.mul_assoc, sigma4_mul_self.2.1, mul_one]
  have h3 : rot4_3 * sigma4_3 = (1 / 2 : ℝ) • fiberJ4 := by
    dsimp [rot4_3]; rw [smul_mul_assoc, Matrix.mul_assoc, sigma4_mul_self.2.2, mul_one]
  rw [h1, h2, h3, smul_smul, ← add_smul, ← add_smul]
  norm_num

private lemma lorJ8_bracket_kron {A B C : Matrix (Fin 4) (Fin 4) ℝ} (h : A * B - B * A = C) :
    lorJ8 A * lorJ8 B - lorJ8 B * lorJ8 A = lorJ8 C := by
  dsimp [lorJ8]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, ← kronecker_sub_right, h]

private lemma lorK8_bracket_kron {A B : Matrix (Fin 4) (Fin 4) ℝ} {C : Matrix (Fin 4) (Fin 4) ℝ}
    (h : A * B - B * A = -((4 : ℝ) • C)) :
    lorK8 A * lorK8 B - lorK8 B * lorK8 A = -(lorJ8 C) := by
  dsimp [lorK8, lorJ8]
  have hZ2 : zCut2 * zCut2 = 1 :=
    real_chiral_circular_peirce_laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hZ2,
    ← smul_sub, ← kronecker_sub_right, h, kronecker_neg24_pol, Matrix.kronecker_smul, smul_neg,
    smul_smul]
  norm_num

private lemma lorJK8_bracket_kron {A B C : Matrix (Fin 4) (Fin 4) ℝ} (h : A * B - B * A = C) :
    lorJ8 A * lorK8 B - lorK8 B * lorJ8 A = lorK8 C := by
  dsimp [lorJ8, lorK8]
  rw [mul_smul_comm, smul_mul_assoc, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, ← smul_sub, ← kronecker_sub_right, h]

/-- **Theorem 1 (Unified `so(3,1)` Algebra, Two Polarized Spin Algebras, & Casimirs on `weylDirac8`)**:
Directly on the real `weylDirac8` carrier `M₂(M₄(ℝ))` (zero complex `i`):
1. `lorJ8` and `lorK8` satisfy all cyclic Lorentz `so(3,1)` commutation relations and commute with `fiberJ8`.
2. Polarization splits `so(3,1)` into **two commuting chiral `su(2)` spin algebras**:
   `spinPlus8_a = P₊ ⊗ S_a` and `spinMinus8_a = P₋ ⊗ S_a` (`[S⁺_a, S⁻_b] = 0`).
3. The Mirror `mirror8` exchanges them (`J_mir S⁺_a J_mir = S⁻_a`).
4. Their chiral Casimirs are `C⁺ = (-3/4) • (P₊ ⊗ I₄)` and `C⁻ = (-3/4) • (P₋ ⊗ I₄)`,
   summing to `J² - K² = (-3/2) • I₈`, and `J₁ K₁ + J₂ K₂ + J₃ K₃ = (3/4) • (Z ⊗ J₄)`. -/
theorem polarized_spin_algebras_on_weylDirac8 :
    let J1 := lorJ8 rot4_1
    let J2 := lorJ8 rot4_2
    let J3 := lorJ8 rot4_3
    let K1 := lorK8 sigma4_1
    let K2 := lorK8 sigma4_2
    let K3 := lorK8 sigma4_3
    let Sp1 := spinPlus8 rot4_1 sigma4_1
    let Sp2 := spinPlus8 rot4_2 sigma4_2
    let Sp3 := spinPlus8 rot4_3 sigma4_3
    let Sm1 := spinMinus8 rot4_1 sigma4_1
    let Sm2 := spinMinus8 rot4_2 sigma4_2
    let Sm3 := spinMinus8 rot4_3 sigma4_3
    (J1 * J2 - J2 * J1 = J3 ∧ J2 * J3 - J3 * J2 = J1 ∧ J3 * J1 - J1 * J3 = J2) ∧
    (K1 * K2 - K2 * K1 = -J3 ∧ K2 * K3 - K3 * K2 = -J1 ∧ K3 * K1 - K1 * K3 = -J2) ∧
    (J1 * K2 - K2 * J1 = K3 ∧ J2 * K3 - K3 * J2 = K1 ∧ J3 * K1 - K1 * J3 = K2) ∧
    (fiberJ8 * J1 = J1 * fiberJ8 ∧ fiberJ8 * K1 = K1 * fiberJ8) ∧
    (Sp1 = pPlus2 ⊗ₖ rot4_1 ∧ Sp2 = pPlus2 ⊗ₖ rot4_2 ∧ Sp3 = pPlus2 ⊗ₖ rot4_3) ∧
    (Sm1 = pMinus2 ⊗ₖ rot4_1 ∧ Sm2 = pMinus2 ⊗ₖ rot4_2 ∧ Sm3 = pMinus2 ⊗ₖ rot4_3) ∧
    (Sp1 * Sp2 - Sp2 * Sp1 = Sp3) ∧
    (Sm1 * Sm2 - Sm2 * Sm1 = Sm3) ∧
    (Sp1 * Sm2 - Sm2 * Sp1 = 0) ∧
    (mirror8 * Sp1 * mirror8 = Sm1 ∧ mirror8 * Sp2 * mirror8 = Sm2 ∧ mirror8 * Sp3 * mirror8 = Sm3) ∧
    (Sp1 * Sp1 + Sp2 * Sp2 + Sp3 * Sp3 = (-3 / 4 : ℝ) • (pPlus2 ⊗ₖ 1)) ∧
    (Sm1 * Sm1 + Sm2 * Sm2 + Sm3 * Sm3 = (-3 / 4 : ℝ) • (pMinus2 ⊗ₖ 1)) ∧
    ((J1 * J1 + J2 * J2 + J3 * J3) - (K1 * K1 + K2 * K2 + K3 * K3) =
      (-3 / 2 : ℝ) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) ∧
    (J1 * K1 + J2 * K2 + J3 * K3 = (3 / 4 : ℝ) • (zCut2 ⊗ₖ fiberJ4)) := by
  have hL := real_chiral_circular_peirce_laws
  have hPp2 : pPlus2 * pPlus2 = pPlus2 := hL.1
  have hPm2 : pMinus2 * pMinus2 = pMinus2 := hL.2.1
  have hPpPm : pPlus2 * pMinus2 = 0 := hL.2.2.1
  have hPmPp : pMinus2 * pPlus2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pPlus2, pMinus2, Matrix.mul_apply, Fin.sum_univ_two]
  have hXppX : xMir2 * pPlus2 * xMir2 = pMinus2 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [xMir2, uPlus2, vMinus2, pPlus2, pMinus2, Matrix.mul_apply, Fin.sum_univ_two]
  have hZ2 : zCut2 * zCut2 = 1 := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hFS1 : fiberJ4 * sigma4_1 = (2 : ℝ) • rot4_1 := by
    dsimp [rot4_1]; rw [smul_smul]; norm_num
  have hFS2 : fiberJ4 * sigma4_2 = (2 : ℝ) • rot4_2 := by
    dsimp [rot4_2]; rw [smul_smul]; norm_num
  have hFS3 : fiberJ4 * sigma4_3 = (2 : ℝ) • rot4_3 := by
    dsimp [rot4_3]; rw [smul_smul]; norm_num
  have hSp1 := spinPlus8_eq_kron rot4_1 sigma4_1 hFS1
  have hSp2 := spinPlus8_eq_kron rot4_2 sigma4_2 hFS2
  have hSp3 := spinPlus8_eq_kron rot4_3 sigma4_3 hFS3
  have hSm1 := spinMinus8_eq_kron rot4_1 sigma4_1 hFS1
  have hSm2 := spinMinus8_eq_kron rot4_2 sigma4_2 hFS2
  have hSm3 := spinMinus8_eq_kron rot4_3 sigma4_3 hFS3
  refine ⟨⟨lorJ8_bracket_kron rot4_1_2, lorJ8_bracket_kron rot4_2_3, lorJ8_bracket_kron rot4_3_1⟩,
    ⟨lorK8_bracket_kron sigma4_1_2, lorK8_bracket_kron sigma4_2_3, lorK8_bracket_kron sigma4_3_1⟩,
    ⟨lorJK8_bracket_kron rot4_1_sigma2, lorJK8_bracket_kron rot4_2_sigma3,
      lorJK8_bracket_kron rot4_3_sigma1⟩,
    ⟨?_, ?_⟩,
    ⟨hSp1, hSp2, hSp3⟩, ⟨hSm1, hSm2, hSm3⟩, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · dsimp [fiberJ8, lorJ8]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul, fiberJ4_rot4_1_comm]
  · dsimp [fiberJ8, lorK8]
    rw [mul_smul_comm, smul_mul_assoc, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      one_mul, mul_one, sigma4_comm_fiberJ4.1]
  · rw [hSp1, hSp2, hSp3, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hPp2,
      ← kronecker_sub_right, rot4_1_2]
  · rw [hSm1, hSm2, hSm3, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hPm2,
      ← kronecker_sub_right, rot4_1_2]
  · rw [hSp1, hSm2, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hPpPm, hPmPp,
      Matrix.zero_kronecker, Matrix.zero_kronecker, sub_zero]
  · dsimp [mirror8]; rw [hSp1, hSm1, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      mul_one, one_mul, hXppX]
  · dsimp [mirror8]; rw [hSp2, hSm2, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      mul_one, one_mul, hXppX]
  · dsimp [mirror8]; rw [hSp3, hSm3, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      mul_one, one_mul, hXppX]
  · rw [hSp1, hSp2, hSp3, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, hPp2, ← Matrix.kronecker_add, ← Matrix.kronecker_add,
      rot4_casimir_sq, Matrix.kronecker_smul]
  · rw [hSm1, hSm2, hSm3, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, hPm2, ← Matrix.kronecker_add, ← Matrix.kronecker_add,
      rot4_casimir_sq, Matrix.kronecker_smul]
  · dsimp [lorJ8, lorK8]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← Matrix.mul_kronecker_mul, one_mul, hZ2,
      sigma4_mul_self.1, sigma4_mul_self.2.1, sigma4_mul_self.2.2,
      ← Matrix.kronecker_add, rot4_casimir_sq, Matrix.kronecker_smul, Matrix.one_kronecker_one]
    rw [← add_smul, ← add_smul, ← sub_smul]
    norm_num
  · dsimp [lorJ8, lorK8]
    simp only [mul_smul_comm, ← Matrix.mul_kronecker_mul, one_mul, ← smul_add,
      ← Matrix.kronecker_add]
    rw [← Matrix.kronecker_smul]
    have hHalfSum : (1 / 2 : ℝ) • (rot4_1 * sigma4_1 + rot4_2 * sigma4_2 + rot4_3 * sigma4_3) =
        (3 / 4 : ℝ) • fiberJ4 := by
      simp only [smul_add]; exact rot4_sigma_prod_half
    rw [hHalfSum, Matrix.kronecker_smul]

/-! ### Part 2: Infinitesimal Lorentz Equivariance, Massive Factorization, & Pauli–Lubanski Casimir -/

private lemma scalar_lorentz_rot1 (a b : ℝ) :
    (1 / 2 : ℝ) * a + -((1 / 2 : ℝ) * b) - (-(1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) = a - b := by
  ring

private lemma scalar_lorentz_rot_neg_sum (a b : ℝ) :
    (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b - (-(1 / 2 : ℝ) * a - (1 / 2 : ℝ) * b) = a + b := by
  ring

private lemma scalar_lorentz_mul_half_sub (x y : ℝ) :
    ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) - ((1 / 2 : ℝ) * (-x) + (1 / 2 : ℝ) * (-y)) = x + y := by
  ring

private lemma scalar_lorentz_half_eq_zero (x : ℝ) :
    (1 / 2 : ℝ) * x + -((1 / 2 : ℝ) * x) = 0 := by
  ring

private lemma scalar_lorentz_half_diff_zero (x y : ℝ) :
    ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) - ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y) = 0 := by
  ring

private lemma scalar_lorentz_half_sum_zero (x : ℝ) :
    (1 / 2 : ℝ) * x - -((1 / 2 : ℝ) * x) - x = 0 := by
  ring

private lemma scalar_lorentz_half_sum_id (x : ℝ) :
    (1 / 2 : ℝ) * x - -((1 / 2 : ℝ) * x) = x := by
  ring

private lemma scalar_lorentz_half_sum_neg (x : ℝ) :
    -(1 / 2 : ℝ) * x - (1 / 2 : ℝ) * x = -x := by
  ring

private lemma scalar_lorentz_boost_diag_add (x₀ x₃ : ℝ) :
    (1 / 2 : ℝ) * (x₀ - x₃) - -((1 / 2 : ℝ) * (x₀ + x₃)) = x₀ := by
  ring

private lemma scalar_lorentz_boost_diag_sub (x₀ x₃ : ℝ) :
    -(1 / 2 : ℝ) * (x₀ + x₃) - (1 / 2 : ℝ) * (x₀ - x₃) = -x₀ := by
  ring

private lemma scalar_spin_half_norm_sq :
    InfoGeometry.Physics.ZornMatrixSU3.dotProduct ![1 / 2, 1 / 2, 1 / 2] ![1 / 2, 1 / 2, 1 / 2] =
      (1 / 2 : ℝ) * ((1 / 2 : ℝ) + 1) := by
  simp [InfoGeometry.Physics.ZornMatrixSU3.dotProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3]
  norm_num

private lemma zCut2_uPlus2_comm : zCut2 * uPlus2 = uPlus2 ∧ uPlus2 * zCut2 = -uPlus2 := by
  constructor <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [zCut2, pPlus2, pMinus2, uPlus2, Matrix.mul_apply, Fin.sum_univ_two] }

private lemma zCut2_vMinus2_comm : zCut2 * vMinus2 = -vMinus2 ∧ vMinus2 * zCut2 = vMinus2 := by
  constructor <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [zCut2, pPlus2, pMinus2, vMinus2, Matrix.mul_apply, Fin.sum_univ_two] }

private lemma lorJ8_comm_weyl (S : Matrix (Fin 4) (Fin 4) ℝ)
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ)
    (h1 : S * realSoldering4 x₀ x₁ x₂ x₃ - realSoldering4 x₀ x₁ x₂ x₃ * S =
      realSoldering4 y₀ y₁ y₂ y₃)
    (h2 : S * realSolderingAdj4 x₀ x₁ x₂ x₃ - realSolderingAdj4 x₀ x₁ x₂ x₃ * S =
      realSolderingAdj4 y₀ y₁ y₂ y₃) :
    lorJ8 S * weylDirac8 x₀ x₁ x₂ x₃ - weylDirac8 x₀ x₁ x₂ x₃ * lorJ8 S =
      weylDirac8 y₀ y₁ y₂ y₃ := by
  dsimp [lorJ8, weylDirac8]
  simp only [mul_add, add_mul, ← Matrix.mul_kronecker_mul, one_mul, mul_one]
  rw [add_sub_add_comm, ← kronecker_sub_right, ← kronecker_sub_right, h1, h2]

private lemma lorK8_comm_weyl (K : Matrix (Fin 4) (Fin 4) ℝ)
    (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ)
    (h1 : (1 / 2 : ℝ) • (K * realSoldering4 x₀ x₁ x₂ x₃ + realSoldering4 x₀ x₁ x₂ x₃ * K) =
      realSoldering4 y₀ y₁ y₂ y₃)
    (h2 : (-(1 / 2 : ℝ)) • (K * realSolderingAdj4 x₀ x₁ x₂ x₃ + realSolderingAdj4 x₀ x₁ x₂ x₃ * K) =
      realSolderingAdj4 y₀ y₁ y₂ y₃) :
    lorK8 K * weylDirac8 x₀ x₁ x₂ x₃ - weylDirac8 x₀ x₁ x₂ x₃ * lorK8 K =
      weylDirac8 y₀ y₁ y₂ y₃ := by
  dsimp [lorK8, weylDirac8]
  rw [smul_mul_assoc, mul_smul_comm, mul_add, add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    zCut2_uPlus2_comm.1, zCut2_uPlus2_comm.2, zCut2_vMinus2_comm.1, zCut2_vMinus2_comm.2,
    neg_kronecker24_pol, neg_kronecker24_pol, ← smul_sub]
  have hReorg :
      (uPlus2 ⊗ₖ (K * realSoldering4 x₀ x₁ x₂ x₃) +
          -(vMinus2 ⊗ₖ (K * realSolderingAdj4 x₀ x₁ x₂ x₃))) -
        (-(uPlus2 ⊗ₖ (realSoldering4 x₀ x₁ x₂ x₃ * K)) +
          vMinus2 ⊗ₖ (realSolderingAdj4 x₀ x₁ x₂ x₃ * K)) =
      uPlus2 ⊗ₖ (K * realSoldering4 x₀ x₁ x₂ x₃ + realSoldering4 x₀ x₁ x₂ x₃ * K) +
        vMinus2 ⊗ₖ (-(K * realSolderingAdj4 x₀ x₁ x₂ x₃ + realSolderingAdj4 x₀ x₁ x₂ x₃ * K)) := by
    rw [Matrix.kronecker_add, kronecker_neg24_pol, Matrix.kronecker_add]
    abel
  rw [hReorg, smul_add, ← Matrix.kronecker_smul, ← Matrix.kronecker_smul, h1, smul_neg, ← neg_smul, h2]

private lemma rot4_1_comm_sold (x₀ x₁ x₂ x₃ : ℝ) :
    rot4_1 * realSoldering4 x₀ x₁ x₂ x₃ - realSoldering4 x₀ x₁ x₂ x₃ * rot4_1 =
      realSoldering4 0 0 (-x₃) x₂ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_1, fiberJ4, sigma4_1, realSoldering4] <;> ring

private lemma rot4_1_comm_adj (x₀ x₁ x₂ x₃ : ℝ) :
    rot4_1 * realSolderingAdj4 x₀ x₁ x₂ x₃ - realSolderingAdj4 x₀ x₁ x₂ x₃ * rot4_1 =
      realSolderingAdj4 0 0 (-x₃) x₂ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_1, fiberJ4, sigma4_1, realSoldering4, realSolderingAdj4] <;> ring

private lemma rot4_2_comm_sold (x₀ x₁ x₂ x₃ : ℝ) :
    rot4_2 * realSoldering4 x₀ x₁ x₂ x₃ - realSoldering4 x₀ x₁ x₂ x₃ * rot4_2 =
      realSoldering4 0 x₃ 0 (-x₁) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_2, fiberJ4, sigma4_2, realSoldering4] <;> ring

private lemma rot4_2_comm_adj (x₀ x₁ x₂ x₃ : ℝ) :
    rot4_2 * realSolderingAdj4 x₀ x₁ x₂ x₃ - realSolderingAdj4 x₀ x₁ x₂ x₃ * rot4_2 =
      realSolderingAdj4 0 x₃ 0 (-x₁) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_2, fiberJ4, sigma4_2, realSoldering4, realSolderingAdj4] <;> ring

private lemma rot4_3_comm_sold (x₀ x₁ x₂ x₃ : ℝ) :
    rot4_3 * realSoldering4 x₀ x₁ x₂ x₃ - realSoldering4 x₀ x₁ x₂ x₃ * rot4_3 =
      realSoldering4 0 (-x₂) x₁ 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_3, fiberJ4, sigma4_3, realSoldering4] <;> ring

private lemma rot4_3_comm_adj (x₀ x₁ x₂ x₃ : ℝ) :
    rot4_3 * realSolderingAdj4 x₀ x₁ x₂ x₃ - realSolderingAdj4 x₀ x₁ x₂ x₃ * rot4_3 =
      realSolderingAdj4 0 (-x₂) x₁ 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot4_3, fiberJ4, sigma4_3, realSoldering4, realSolderingAdj4] <;> ring

private lemma sigma4_1_anti_sold (x₀ x₁ x₂ x₃ : ℝ) :
    (1 / 2 : ℝ) • (sigma4_1 * realSoldering4 x₀ x₁ x₂ x₃ + realSoldering4 x₀ x₁ x₂ x₃ * sigma4_1) =
      realSoldering4 x₁ x₀ 0 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma4_1, realSoldering4] <;> ring

private lemma sigma4_1_anti_adj (x₀ x₁ x₂ x₃ : ℝ) :
    (-(1 / 2 : ℝ)) • (sigma4_1 * realSolderingAdj4 x₀ x₁ x₂ x₃ +
        realSolderingAdj4 x₀ x₁ x₂ x₃ * sigma4_1) =
      realSolderingAdj4 x₁ x₀ 0 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma4_1, realSoldering4, realSolderingAdj4] <;> ring

private lemma sigma4_2_anti_sold (x₀ x₁ x₂ x₃ : ℝ) :
    (1 / 2 : ℝ) • (sigma4_2 * realSoldering4 x₀ x₁ x₂ x₃ + realSoldering4 x₀ x₁ x₂ x₃ * sigma4_2) =
      realSoldering4 x₂ 0 x₀ 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma4_2, realSoldering4] <;> ring

private lemma sigma4_2_anti_adj (x₀ x₁ x₂ x₃ : ℝ) :
    (-(1 / 2 : ℝ)) • (sigma4_2 * realSolderingAdj4 x₀ x₁ x₂ x₃ +
        realSolderingAdj4 x₀ x₁ x₂ x₃ * sigma4_2) =
      realSolderingAdj4 x₂ 0 x₀ 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma4_2, realSoldering4, realSolderingAdj4] <;> ring

private lemma sigma4_3_anti_sold (x₀ x₁ x₂ x₃ : ℝ) :
    (1 / 2 : ℝ) • (sigma4_3 * realSoldering4 x₀ x₁ x₂ x₃ + realSoldering4 x₀ x₁ x₂ x₃ * sigma4_3) =
      realSoldering4 x₃ 0 0 x₀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma4_3, realSoldering4] <;> ring

private lemma sigma4_3_anti_adj (x₀ x₁ x₂ x₃ : ℝ) :
    (-(1 / 2 : ℝ)) • (sigma4_3 * realSolderingAdj4 x₀ x₁ x₂ x₃ +
        realSolderingAdj4 x₀ x₁ x₂ x₃ * sigma4_3) =
      realSolderingAdj4 x₃ 0 0 x₀ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma4_3, realSoldering4, realSolderingAdj4] <;> ring

/-- **Theorem 2 (Lorentz Equivariance of `weylDirac8`, Massive Factorization, & Pauli–Lubanski Casimir)**:
1. Infinitesimal rotation & boost equivariance directly on lifted 4-vectors inside `weylDirac8`
   for all spatial axes `a ∈ {1, 2, 3}`:
   `[J₁, D(x)] = D(0, 0, -x₃, x₂)`, `[J₂, D(x)] = D(0, x₃, 0, -x₁)`, `[J₃, D(x)] = D(0, -x₂, x₁, 0)`,
   `[K₁, D(x)] = D(x₁, x₀, 0, 0)`, `[K₂, D(x)] = D(x₂, 0, x₀, 0)`, `[K₃, D(x)] = D(x₃, 0, 0, x₀)`.
2. **Massive Dirac Factorization**:
   `(D(p) - m • I₈) * (D(p) + m • I₈) = (p₀² - p₁² - p₂² - p₃² - m²) • I₈`.
3. **Rest-Frame Mirror Coupling & Pauli–Lubanski Spin-`1/2` Casimir**:
   At rest `p = (m, 0, 0, 0)`, `D(m, 0, 0, 0) = m • mirror8`,
   `W² := (m • J₁)² + (m • J₂)² + (m • J₃)² = (-3/4 * m²) • I₈`, matching
   `OperatorPauliLubanskiLift.rest_frame_massive_casimir` at `s = 1/2`. -/
theorem weylDirac8_lorentz_equivariance_and_massive_casimir (x₀ x₁ x₂ x₃ m : ℝ) :
    let D := weylDirac8 x₀ x₁ x₂ x₃
    let J1 := lorJ8 rot4_1
    let J2 := lorJ8 rot4_2
    let J3 := lorJ8 rot4_3
    let K1 := lorK8 sigma4_1
    let K2 := lorK8 sigma4_2
    let K3 := lorK8 sigma4_3
    (J1 * D - D * J1 = weylDirac8 0 0 (-x₃) x₂) ∧
    (J2 * D - D * J2 = weylDirac8 0 x₃ 0 (-x₁)) ∧
    (J3 * D - D * J3 = weylDirac8 0 (-x₂) x₁ 0) ∧
    (K1 * D - D * K1 = weylDirac8 x₁ x₀ 0 0) ∧
    (K2 * D - D * K2 = weylDirac8 x₂ 0 x₀ 0) ∧
    (K3 * D - D * K3 = weylDirac8 x₃ 0 0 x₀) ∧
    ((D - m • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) *
      (D + m • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 - m ^ 2) •
        (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) ∧
    (weylDirac8 m 0 0 0 = m • mirror8) ∧
    ((m • J1) * (m • J1) + (m • J2) * (m • J2) + (m • J3) * (m • J3) =
      (-3 / 4 * m ^ 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) ∧
    (InfoGeometry.Physics.LorentzBoostMinkowski.minkowskiPair
        (InfoGeometry.Physics.PauliLubanskiFiniteBridge.pauliLubanski
          ⟨⟨m, 0, 0, 0⟩, ![1 / 2, 1 / 2, 1 / 2], 0⟩)
        (InfoGeometry.Physics.PauliLubanskiFiniteBridge.pauliLubanski
          ⟨⟨m, 0, 0, 0⟩, ![1 / 2, 1 / 2, 1 / 2], 0⟩) =
      -m ^ 2 * (1 / 2 : ℝ) * ((1 / 2 : ℝ) + 1)) := by
  have hU := unified_weyl_dirac8_and_susy_block x₀ x₁ x₂ x₃ x₀ x₁ x₂ x₃ 0 0 0 0
  have hD2 : weylDirac8 x₀ x₁ x₂ x₃ * weylDirac8 x₀ x₁ x₂ x₃ =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) •
        (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) := hU.2.2.2.2.1
  have hFactM :
      (weylDirac8 x₀ x₁ x₂ x₃ - m • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) *
        (weylDirac8 x₀ x₁ x₂ x₃ + m • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 - m ^ 2) •
        (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) := by
    have h1 : weylDirac8 x₀ x₁ x₂ x₃ * (m • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) =
        m • weylDirac8 x₀ x₁ x₂ x₃ := by rw [mul_smul_comm, mul_one]
    have h2 : (m • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) * weylDirac8 x₀ x₁ x₂ x₃ =
        m • weylDirac8 x₀ x₁ x₂ x₃ := by rw [smul_mul_assoc, one_mul]
    have h3 : (m • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) *
        (m • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ)) =
        m ^ 2 • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) := by
      rw [smul_mul_assoc, one_mul, smul_smul, ← sq]
    rw [sub_mul, mul_add, mul_add, hD2, h1, h2, h3, sub_smul]
    module
  have hCas :
      (m • lorJ8 rot4_1) * (m • lorJ8 rot4_1) +
      (m • lorJ8 rot4_2) * (m • lorJ8 rot4_2) +
      (m • lorJ8 rot4_3) * (m • lorJ8 rot4_3) =
      (-3 / 4 * m ^ 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, lorJ8, ← Matrix.mul_kronecker_mul,
      one_mul, ← smul_add, ← Matrix.kronecker_add, rot4_casimir_sq, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
    have hScalar : m * m * (-3 / 4 : ℝ) = -3 / 4 * m ^ 2 := by
      have hm2 : m * m = m ^ 2 := (sq m).symm
      rw [hm2, mul_comm (m ^ 2) (-3 / 4 : ℝ)]
    rw [hScalar]
  have hPL := InfoGeometry.Bridge.OperatorPauliLubanskiLift.rest_frame_massive_casimir
    m (1 / 2) ![1 / 2, 1 / 2, 1 / 2] 0 scalar_spin_half_norm_sq
  have hRestM : weylDirac8 m 0 0 0 = m • mirror8 := by
    have hM : realSoldering4 m 0 0 0 = m • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [realSoldering4]
    have hAdj : realSolderingAdj4 m 0 0 0 = m • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [realSolderingAdj4]
    dsimp [weylDirac8, mirror8, xMir2]
    rw [hM, hAdj, Matrix.kronecker_smul, Matrix.kronecker_smul, ← smul_add, ← Matrix.add_kronecker]
  exact ⟨lorJ8_comm_weyl rot4_1 x₀ x₁ x₂ x₃ 0 0 (-x₃) x₂ (rot4_1_comm_sold _ _ _ _) (rot4_1_comm_adj _ _ _ _),
    lorJ8_comm_weyl rot4_2 x₀ x₁ x₂ x₃ 0 x₃ 0 (-x₁) (rot4_2_comm_sold _ _ _ _) (rot4_2_comm_adj _ _ _ _),
    lorJ8_comm_weyl rot4_3 x₀ x₁ x₂ x₃ 0 (-x₂) x₁ 0 (rot4_3_comm_sold _ _ _ _) (rot4_3_comm_adj _ _ _ _),
    lorK8_comm_weyl sigma4_1 x₀ x₁ x₂ x₃ x₁ x₀ 0 0 (sigma4_1_anti_sold _ _ _ _) (sigma4_1_anti_adj _ _ _ _),
    lorK8_comm_weyl sigma4_2 x₀ x₁ x₂ x₃ x₂ 0 x₀ 0 (sigma4_2_anti_sold _ _ _ _) (sigma4_2_anti_adj _ _ _ _),
    lorK8_comm_weyl sigma4_3 x₀ x₁ x₂ x₃ x₃ 0 0 x₀ (sigma4_3_anti_sold _ _ _ _) (sigma4_3_anti_adj _ _ _ _),
    hFactM, hRestM, hCas, hPL⟩

/-! ### Part 3: Finite Spinor Lorentz Boosts & Spatial Rotations (`SL(2,ℂ)_ℝ ⊂ M₈(ℝ)`) -/

/-- Finite spinor Lorentz boost along axis `x₁`: `exp(t 𝒦₁) = cosh(t/2) I₈ + sinh(t/2) (2 𝒦₁)`. -/
def boostRotor8_1 (t : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  Real.cosh (t / 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) +
    Real.sinh (t / 2) • ((2 : ℝ) • lorK8 sigma4_1)

/-- Finite spinor Lorentz boost along axis `x₃`: `exp(t 𝒦₃) = cosh(t/2) I₈ + sinh(t/2) (2 𝒦₃)`. -/
def boostRotor8_3 (t : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  Real.cosh (t / 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) +
    Real.sinh (t / 2) • ((2 : ℝ) • lorK8 sigma4_3)

/-- Finite spinor spatial rotation around axis `x₁`: `exp(θ 𝒥₁) = cos(θ/2) I₈ + sin(θ/2) (2 𝒥₁)`. -/
def rotRotor8_1 (θ : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ :=
  Real.cos (θ / 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) +
    Real.sin (θ / 2) • ((2 : ℝ) • lorJ8 rot4_1)

private lemma scalar_hyp_rotor_mul_c (a b : ℝ) :
    Real.cosh ((a + b) / 2) = Real.cosh (a / 2) * Real.cosh (b / 2) + Real.sinh (a / 2) * Real.sinh (b / 2) := by
  have h := Real.cosh_add (a / 2) (b / 2)
  rw [← add_div] at h
  exact h

private lemma scalar_hyp_rotor_mul_s (a b : ℝ) :
    Real.sinh ((a + b) / 2) = Real.sinh (a / 2) * Real.cosh (b / 2) + Real.cosh (a / 2) * Real.sinh (b / 2) := by
  have h := Real.sinh_add (a / 2) (b / 2)
  rw [← add_div] at h
  exact h

private lemma scalar_trig_rotor_mul_c (a b : ℝ) :
    Real.cos ((a + b) / 2) = Real.cos (a / 2) * Real.cos (b / 2) - Real.sin (a / 2) * Real.sin (b / 2) := by
  have h := Real.cos_add (a / 2) (b / 2)
  rw [← add_div] at h
  exact h

private lemma scalar_trig_rotor_mul_s (a b : ℝ) :
    Real.sin ((a + b) / 2) = Real.sin (a / 2) * Real.cos (b / 2) + Real.cos (a / 2) * Real.sin (b / 2) := by
  have h := Real.sin_add (a / 2) (b / 2)
  rw [← add_div] at h
  exact h

private lemma scalar_cosh_two_half (t : ℝ) :
    Real.cosh (t / 2) * Real.cosh (t / 2) + Real.sinh (t / 2) * Real.sinh (t / 2) = Real.cosh t := by
  have h := Real.cosh_add (t / 2) (t / 2)
  have ht : t / 2 + t / 2 = t := add_halves t
  rw [ht] at h
  exact h.symm

private lemma scalar_sinh_two_half (t : ℝ) :
    Real.sinh (t / 2) * Real.cosh (t / 2) + Real.cosh (t / 2) * Real.sinh (t / 2) = Real.sinh t := by
  have h := Real.sinh_add (t / 2) (t / 2)
  have ht : t / 2 + t / 2 = t := add_halves t
  rw [ht] at h
  exact h.symm

private lemma scalar_cos_two_half (θ : ℝ) :
    Real.cos (θ / 2) * Real.cos (θ / 2) - Real.sin (θ / 2) * Real.sin (θ / 2) = Real.cos θ := by
  have h := Real.cos_add (θ / 2) (θ / 2)
  have ht : θ / 2 + θ / 2 = θ := add_halves θ
  rw [ht] at h
  exact h.symm

private lemma scalar_sin_two_half (θ : ℝ) :
    Real.sin (θ / 2) * Real.cos (θ / 2) + Real.cos (θ / 2) * Real.sin (θ / 2) = Real.sin θ := by
  have h := Real.sin_add (θ / 2) (θ / 2)
  have ht : θ / 2 + θ / 2 = θ := add_halves θ
  rw [ht] at h
  exact h.symm

private lemma scalar_hyp_sq_diff (t : ℝ) :
    Real.cosh (t / 2) * Real.cosh (t / 2) - Real.sinh (t / 2) * Real.sinh (t / 2) = 1 := by
  simpa [sq] using Real.cosh_sq_sub_sinh_sq (t / 2)

private lemma scalar_trig_sq_sum (θ : ℝ) :
    Real.cos (θ / 2) * Real.cos (θ / 2) + Real.sin (θ / 2) * Real.sin (θ / 2) = 1 := by
  simpa [sq] using Real.cos_sq_add_sin_sq (θ / 2)

private lemma realSoldering4_add (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ) :
    realSoldering4 x₀ x₁ x₂ x₃ + realSoldering4 y₀ y₁ y₂ y₃ =
      realSoldering4 (x₀ + y₀) (x₁ + y₁) (x₂ + y₂) (x₃ + y₃) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realSoldering4] <;> ring

private lemma realSolderingAdj4_add (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ) :
    realSolderingAdj4 x₀ x₁ x₂ x₃ + realSolderingAdj4 y₀ y₁ y₂ y₃ =
      realSolderingAdj4 (x₀ + y₀) (x₁ + y₁) (x₂ + y₂) (x₃ + y₃) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realSolderingAdj4] <;> ring

private lemma realSoldering4_smul (c x₀ x₁ x₂ x₃ : ℝ) :
    c • realSoldering4 x₀ x₁ x₂ x₃ = realSoldering4 (c * x₀) (c * x₁) (c * x₂) (c * x₃) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realSoldering4] <;> ring

private lemma realSolderingAdj4_smul (c x₀ x₁ x₂ x₃ : ℝ) :
    c • realSolderingAdj4 x₀ x₁ x₂ x₃ =
      realSolderingAdj4 (c * x₀) (c * x₁) (c * x₂) (c * x₃) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [realSolderingAdj4] <;> ring

private lemma weylDirac8_linear_add (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ) :
    weylDirac8 x₀ x₁ x₂ x₃ + weylDirac8 y₀ y₁ y₂ y₃ =
      weylDirac8 (x₀ + y₀) (x₁ + y₁) (x₂ + y₂) (x₃ + y₃) := by
  dsimp [weylDirac8]
  rw [add_add_add_comm, ← Matrix.kronecker_add, ← Matrix.kronecker_add,
    realSoldering4_add, realSolderingAdj4_add]

private lemma weylDirac8_linear_smul (c x₀ x₁ x₂ x₃ : ℝ) :
    c • weylDirac8 x₀ x₁ x₂ x₃ = weylDirac8 (c * x₀) (c * x₁) (c * x₂) (c * x₃) := by
  dsimp [weylDirac8]
  rw [smul_add, ← Matrix.kronecker_smul, ← Matrix.kronecker_smul,
    realSoldering4_smul, realSolderingAdj4_smul]

private lemma invol_rotor_mul
    {G : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ}
    (hG2 : G * G = 1) (c₁ s₁ c₂ s₂ : ℝ) :
    (c₁ • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s₁ • G) * (c₂ • 1 + s₂ • G) =
      (c₁ * c₂ + s₁ * s₂) • 1 + (s₁ * c₂ + c₁ * s₂) • G := by
  simp only [add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, hG2]
  rw [add_smul, add_smul]
  module

private lemma skew_rotor_mul
    {G : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ}
    (hG2 : G * G = -1) (c₁ s₁ c₂ s₂ : ℝ) :
    (c₁ • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s₁ • G) * (c₂ • 1 + s₂ • G) =
      (c₁ * c₂ - s₁ * s₂) • 1 + (s₁ * c₂ + c₁ * s₂) • G := by
  simp only [add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, hG2, smul_neg]
  rw [sub_smul, add_smul]
  module

private lemma invol_conj_anticomm
    {G D : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ}
    (hG2 : G * G = 1) (hAnti : G * D = -(D * G)) (c s : ℝ) :
    (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D * (c • 1 - s • G) =
      (c * c + s * s) • D + (s * c + c * s) • (G * D) := by
  have hComm : (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D =
      D * (c • 1 - s • G) := by
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hAnti, smul_neg]
    rw [sub_eq_add_neg]
  have hLhs : (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D * (c • 1 - s • G) =
      ((c • 1 + s • G) * (c • 1 + s • G)) * D := by
    calc
      (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D * (c • 1 - s • G)
          = (c • 1 + s • G) * (D * (c • 1 - s • G)) := Matrix.mul_assoc _ _ _
      _ = (c • 1 + s • G) * ((c • 1 + s • G) * D) := by rw [← hComm]
      _ = ((c • 1 + s • G) * (c • 1 + s • G)) * D := (Matrix.mul_assoc _ _ _).symm
  rw [hLhs, invol_rotor_mul hG2 c s c s, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]

private lemma scalar_rotor_cancel (c s : ℝ) : s * c + -(c * s) = 0 := by ring
private lemma scalar_rotor_diff (c s : ℝ) : c * c + -(s * s) = c * c - s * s := by ring
private lemma scalar_rotor_sum (c s : ℝ) : s * c + -(c * s) = 0 := by ring

private lemma invol_conj_comm
    {G D : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ}
    (hG2 : G * G = 1) (hComm : G * D = D * G) (c s : ℝ) :
    (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D * (c • 1 - s • G) =
      (c * c - s * s) • D := by
  have hCommR : D * (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) - s • G) =
      (c • 1 - s • G) * D := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hComm]
  rw [Matrix.mul_assoc, hCommR, ← Matrix.mul_assoc, sub_eq_add_neg (c • 1), ← neg_smul,
    invol_rotor_mul hG2 c s c (-s)]
  simp only [mul_neg]
  rw [scalar_rotor_cancel, scalar_rotor_diff, zero_smul, add_zero, smul_mul_assoc, one_mul]

private lemma skew_conj_anticomm
    {G D : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ}
    (hG2 : G * G = -1) (hAnti : G * D = -(D * G)) (c s : ℝ) :
    (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D * (c • 1 - s • G) =
      (c * c - s * s) • D + (s * c + c * s) • (G * D) := by
  have hComm : (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D =
      D * (c • 1 - s • G) := by
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hAnti, smul_neg]
    rw [sub_eq_add_neg]
  have hLhs : (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D * (c • 1 - s • G) =
      ((c • 1 + s • G) * (c • 1 + s • G)) * D := by
    calc
      (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D * (c • 1 - s • G)
          = (c • 1 + s • G) * (D * (c • 1 - s • G)) := Matrix.mul_assoc _ _ _
      _ = (c • 1 + s • G) * ((c • 1 + s • G) * D) := by rw [← hComm]
      _ = ((c • 1 + s • G) * (c • 1 + s • G)) * D := (Matrix.mul_assoc _ _ _).symm
  rw [hLhs, skew_rotor_mul hG2 c s c s, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]

private lemma skew_conj_comm
    {G D : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ}
    (hG2 : G * G = -1) (hComm : G * D = D * G) (c s : ℝ) :
    (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + s • G) * D * (c • 1 - s • G) =
      (c * c + s * s) • D := by
  have hCommR : D * (c • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) - s • G) =
      (c • 1 - s • G) * D := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hComm]
  rw [Matrix.mul_assoc, hCommR, ← Matrix.mul_assoc, sub_eq_add_neg (c • 1), ← neg_smul,
    skew_rotor_mul hG2 c s c (-s)]
  simp only [mul_neg, sub_neg_eq_add]
  rw [scalar_rotor_sum, zero_smul, add_zero, smul_mul_assoc]
  rw [one_mul]

private lemma k1_para_lemma (x₀ x₁ : ℝ) :
    ((2 : ℝ) • lorK8 sigma4_1) * weylDirac8 x₀ x₁ 0 0 =
      -(weylDirac8 x₀ x₁ 0 0 * ((2 : ℝ) • lorK8 sigma4_1)) := by
  have hS : sigma4_1 * realSoldering4 x₀ x₁ 0 0 = realSoldering4 x₀ x₁ 0 0 * sigma4_1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sigma4_1, realSoldering4]
  have hA : sigma4_1 * realSolderingAdj4 x₀ x₁ 0 0 = realSolderingAdj4 x₀ x₁ 0 0 * sigma4_1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sigma4_1, realSoldering4, realSolderingAdj4]
  have hTwoK : (2 : ℝ) • lorK8 sigma4_1 = zCut2 ⊗ₖ sigma4_1 := by
    dsimp [lorK8]; rw [smul_smul]; norm_num
  rw [hTwoK]
  dsimp [weylDirac8]
  rw [mul_add, add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    zCut2_uPlus2_comm.1, zCut2_uPlus2_comm.2, zCut2_vMinus2_comm.1, zCut2_vMinus2_comm.2,
    hS, hA, neg_kronecker24_pol, neg_kronecker24_pol]
  abel

private lemma k1_perp_lemma (x₂ x₃ : ℝ) :
    ((2 : ℝ) • lorK8 sigma4_1) * weylDirac8 0 0 x₂ x₃ =
      weylDirac8 0 0 x₂ x₃ * ((2 : ℝ) • lorK8 sigma4_1) := by
  have hS : sigma4_1 * realSoldering4 0 0 x₂ x₃ = -(realSoldering4 0 0 x₂ x₃ * sigma4_1) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sigma4_1, realSoldering4]
  have hA : sigma4_1 * realSolderingAdj4 0 0 x₂ x₃ =
      -(realSolderingAdj4 0 0 x₂ x₃ * sigma4_1) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sigma4_1, realSoldering4, realSolderingAdj4]
  have hTwoK : (2 : ℝ) • lorK8 sigma4_1 = zCut2 ⊗ₖ sigma4_1 := by
    dsimp [lorK8]; rw [smul_smul]; norm_num
  rw [hTwoK]
  dsimp [weylDirac8]
  rw [mul_add, add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    zCut2_uPlus2_comm.1, zCut2_uPlus2_comm.2, zCut2_vMinus2_comm.1, zCut2_vMinus2_comm.2,
    hS, hA, neg_kronecker24_pol, neg_kronecker24_pol, kronecker_neg24_pol, kronecker_neg24_pol,
    neg_neg]

private lemma k3_para_lemma (x₀ x₃ : ℝ) :
    ((2 : ℝ) • lorK8 sigma4_3) * weylDirac8 x₀ 0 0 x₃ =
      -(weylDirac8 x₀ 0 0 x₃ * ((2 : ℝ) • lorK8 sigma4_3)) := by
  have hS : sigma4_3 * realSoldering4 x₀ 0 0 x₃ = realSoldering4 x₀ 0 0 x₃ * sigma4_3 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sigma4_3, realSoldering4]
  have hA : sigma4_3 * realSolderingAdj4 x₀ 0 0 x₃ = realSolderingAdj4 x₀ 0 0 x₃ * sigma4_3 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sigma4_3, realSoldering4, realSolderingAdj4]
  have hTwoK : (2 : ℝ) • lorK8 sigma4_3 = zCut2 ⊗ₖ sigma4_3 := by
    dsimp [lorK8]; rw [smul_smul]; norm_num
  rw [hTwoK]
  dsimp [weylDirac8]
  rw [mul_add, add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    zCut2_uPlus2_comm.1, zCut2_uPlus2_comm.2, zCut2_vMinus2_comm.1, zCut2_vMinus2_comm.2,
    hS, hA, neg_kronecker24_pol, neg_kronecker24_pol]
  abel

private lemma k3_perp_lemma (x₁ x₂ : ℝ) :
    ((2 : ℝ) • lorK8 sigma4_3) * weylDirac8 0 x₁ x₂ 0 =
      weylDirac8 0 x₁ x₂ 0 * ((2 : ℝ) • lorK8 sigma4_3) := by
  have hS : sigma4_3 * realSoldering4 0 x₁ x₂ 0 = -(realSoldering4 0 x₁ x₂ 0 * sigma4_3) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sigma4_3, realSoldering4]
  have hA : sigma4_3 * realSolderingAdj4 0 x₁ x₂ 0 =
      -(realSolderingAdj4 0 x₁ x₂ 0 * sigma4_3) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sigma4_3, realSoldering4, realSolderingAdj4]
  have hTwoK : (2 : ℝ) • lorK8 sigma4_3 = zCut2 ⊗ₖ sigma4_3 := by
    dsimp [lorK8]; rw [smul_smul]; norm_num
  rw [hTwoK]
  dsimp [weylDirac8]
  rw [mul_add, add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    zCut2_uPlus2_comm.1, zCut2_uPlus2_comm.2, zCut2_vMinus2_comm.1, zCut2_vMinus2_comm.2,
    hS, hA, neg_kronecker24_pol, neg_kronecker24_pol, kronecker_neg24_pol, kronecker_neg24_pol,
    neg_neg]

private lemma j1_para_lemma (x₂ x₃ : ℝ) :
    ((2 : ℝ) • lorJ8 rot4_1) * weylDirac8 0 0 x₂ x₃ =
      -(weylDirac8 0 0 x₂ x₃ * ((2 : ℝ) • lorJ8 rot4_1)) := by
  have hS : ((2 : ℝ) • rot4_1) * realSoldering4 0 0 x₂ x₃ =
      -(realSoldering4 0 0 x₂ x₃ * ((2 : ℝ) • rot4_1)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rot4_1, fiberJ4, sigma4_1, realSoldering4]
  have hA : ((2 : ℝ) • rot4_1) * realSolderingAdj4 0 0 x₂ x₃ =
      -(realSolderingAdj4 0 0 x₂ x₃ * ((2 : ℝ) • rot4_1)) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rot4_1, fiberJ4, sigma4_1, realSoldering4, realSolderingAdj4]
  have hTwoJ : (2 : ℝ) • lorJ8 rot4_1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ ((2 : ℝ) • rot4_1) := by
    dsimp [lorJ8]; rw [Matrix.kronecker_smul]
  rw [hTwoJ]
  dsimp [weylDirac8]
  rw [mul_add, add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [one_mul, mul_one, hS, hA, kronecker_neg24_pol, neg_add]

private lemma j1_perp_lemma (x₀ x₁ : ℝ) :
    ((2 : ℝ) • lorJ8 rot4_1) * weylDirac8 x₀ x₁ 0 0 =
      weylDirac8 x₀ x₁ 0 0 * ((2 : ℝ) • lorJ8 rot4_1) := by
  have hS : ((2 : ℝ) • rot4_1) * realSoldering4 x₀ x₁ 0 0 =
      realSoldering4 x₀ x₁ 0 0 * ((2 : ℝ) • rot4_1) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rot4_1, fiberJ4, sigma4_1, realSoldering4]
  have hA : ((2 : ℝ) • rot4_1) * realSolderingAdj4 x₀ x₁ 0 0 =
      realSolderingAdj4 x₀ x₁ 0 0 * ((2 : ℝ) • rot4_1) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rot4_1, fiberJ4, sigma4_1, realSoldering4, realSolderingAdj4]
  have hTwoJ : (2 : ℝ) • lorJ8 rot4_1 = (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ ((2 : ℝ) • rot4_1) := by
    dsimp [lorJ8]; rw [Matrix.kronecker_smul]
  rw [hTwoJ]
  dsimp [weylDirac8]
  rw [mul_add, add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [one_mul, mul_one, hS, hA]

/-- **Theorem 3 (Finite Spinor Lorentz Boosts & Spatial Rotations `SL(2,ℂ)_ℝ ⊂ M₈(ℝ)`)**:
1. Exact finite rotor group laws and inverse identities for `boostRotor8_1`, `boostRotor8_3`, `rotRotor8_1`.
2. **Exact Finite Boost Covariance**:
   `boostRotor8_1 t * D(x) * boostRotor8_1 (-t) = D(cosh t x₀ + sinh t x₁, sinh t x₀ + cosh t x₁, x₂, x₃)` and
   `boostRotor8_3 t * D(x) * boostRotor8_3 (-t) = D(cosh t x₀ + sinh t x₃, x₁, x₂, sinh t x₀ + cosh t x₃)`.
3. **Exact Finite Spatial Rotation Covariance**:
   `rotRotor8_1 θ * D(x) * rotRotor8_1 (-θ) = D(x₀, x₁, cos θ x₂ - sin θ x₃, sin θ x₂ + cos θ x₃)`.
4. **Longitudinal `k=1` Mirror / OS Boost Lift**:
   `lorentzBoost2 η ⊗ₖ I₄ = cosh η • I₈ + sinh η • mirror8` and
   `(½ • transferMatHyp J) ⊗ₖ I₄ = cosh J • I₈ + sinh J • mirror8`. -/
theorem finite_lorentz_boost_and_rotation_covariance_weylDirac8
    (t₁ t₂ θ₁ θ₂ t θ x₀ x₁ x₂ x₃ η J : ℝ) :
    (boostRotor8_1 t₁ * boostRotor8_1 t₂ = boostRotor8_1 (t₁ + t₂)) ∧
    (boostRotor8_1 t * boostRotor8_1 (-t) = 1) ∧
    (boostRotor8_3 t₁ * boostRotor8_3 t₂ = boostRotor8_3 (t₁ + t₂)) ∧
    (boostRotor8_3 t * boostRotor8_3 (-t) = 1) ∧
    (rotRotor8_1 θ₁ * rotRotor8_1 θ₂ = rotRotor8_1 (θ₁ + θ₂)) ∧
    (rotRotor8_1 θ * rotRotor8_1 (-θ) = 1) ∧
    (boostRotor8_1 t * weylDirac8 x₀ x₁ x₂ x₃ * boostRotor8_1 (-t) =
      weylDirac8 (Real.cosh t * x₀ + Real.sinh t * x₁) (Real.sinh t * x₀ + Real.cosh t * x₁) x₂ x₃) ∧
    (boostRotor8_3 t * weylDirac8 x₀ x₁ x₂ x₃ * boostRotor8_3 (-t) =
      weylDirac8 (Real.cosh t * x₀ + Real.sinh t * x₃) x₁ x₂ (Real.sinh t * x₀ + Real.cosh t * x₃)) ∧
    (rotRotor8_1 θ * weylDirac8 x₀ x₁ x₂ x₃ * rotRotor8_1 (-θ) =
      weylDirac8 x₀ x₁ (Real.cos θ * x₂ - Real.sin θ * x₃) (Real.sin θ * x₂ + Real.cos θ * x₃)) ∧
    (InfoGeometry.LLM.KreinPositionalThermodynamicAttention.lorentzBoost2 η ⊗ₖ
        (1 : Matrix (Fin 4) (Fin 4) ℝ) =
      Real.cosh η • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + Real.sinh η • mirror8) ∧
    (((1 / 2 : ℝ) • InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap.transferMatHyp J) ⊗ₖ
        (1 : Matrix (Fin 4) (Fin 4) ℝ) =
      Real.cosh J • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + Real.sinh J • mirror8) := by
  have hK1_sq : ((2 : ℝ) • lorK8 sigma4_1) * ((2 : ℝ) • lorK8 sigma4_1) = 1 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, lorK8, ← Matrix.mul_kronecker_mul]
    have hZ2 : zCut2 * zCut2 = 1 :=
      real_chiral_circular_peirce_laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [hZ2, sigma4_mul_self.1, Matrix.one_kronecker_one]
    norm_num
  have hK3_sq : ((2 : ℝ) • lorK8 sigma4_3) * ((2 : ℝ) • lorK8 sigma4_3) = 1 := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, lorK8, ← Matrix.mul_kronecker_mul]
    have hZ2 : zCut2 * zCut2 = 1 :=
      real_chiral_circular_peirce_laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [hZ2, sigma4_mul_self.2.2, Matrix.one_kronecker_one]
    norm_num
  have hJ1_sq : ((2 : ℝ) • lorJ8 rot4_1) * ((2 : ℝ) • lorJ8 rot4_1) = -1 := by
    dsimp [lorJ8]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← Matrix.mul_kronecker_mul, one_mul, rot4_1_sq,
      Matrix.kronecker_smul, smul_smul, Matrix.one_kronecker_one]
    norm_num
  have hB1_mul : ∀ a b : ℝ, boostRotor8_1 a * boostRotor8_1 b = boostRotor8_1 (a + b) := by
    intro a b
    unfold boostRotor8_1
    rw [invol_rotor_mul hK1_sq, ← scalar_hyp_rotor_mul_c, ← scalar_hyp_rotor_mul_s]
  have hB3_mul : ∀ a b : ℝ, boostRotor8_3 a * boostRotor8_3 b = boostRotor8_3 (a + b) := by
    intro a b
    unfold boostRotor8_3
    rw [invol_rotor_mul hK3_sq, ← scalar_hyp_rotor_mul_c, ← scalar_hyp_rotor_mul_s]
  have hR1_mul : ∀ a b : ℝ, rotRotor8_1 a * rotRotor8_1 b = rotRotor8_1 (a + b) := by
    intro a b
    unfold rotRotor8_1
    rw [skew_rotor_mul hJ1_sq, ← scalar_trig_rotor_mul_c, ← scalar_trig_rotor_mul_s]
  have hB1_inv : boostRotor8_1 t * boostRotor8_1 (-t) = 1 := by
    rw [hB1_mul, add_neg_cancel]
    simp [boostRotor8_1, Real.cosh_zero, Real.sinh_zero]
  have hB3_inv : boostRotor8_3 t * boostRotor8_3 (-t) = 1 := by
    rw [hB3_mul, add_neg_cancel]
    simp [boostRotor8_3, Real.cosh_zero, Real.sinh_zero]
  have hR1_inv : rotRotor8_1 θ * rotRotor8_1 (-θ) = 1 := by
    rw [hR1_mul, add_neg_cancel]
    simp [rotRotor8_1, Real.cos_zero, Real.sin_zero]
  -- Algebraic conjugation steps via para/perp decompositions:
  have hB1_neg : boostRotor8_1 (-t) =
      Real.cosh (t / 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) -
        Real.sinh (t / 2) • ((2 : ℝ) • lorK8 sigma4_1) := by
    unfold boostRotor8_1
    rw [neg_div, Real.cosh_neg, Real.sinh_neg, neg_smul, sub_eq_add_neg]
  have hB3_neg : boostRotor8_3 (-t) =
      Real.cosh (t / 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) -
        Real.sinh (t / 2) • ((2 : ℝ) • lorK8 sigma4_3) := by
    unfold boostRotor8_3
    rw [neg_div, Real.cosh_neg, Real.sinh_neg, neg_smul, sub_eq_add_neg]
  have hR1_neg : rotRotor8_1 (-θ) =
      Real.cos (θ / 2) • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) -
        Real.sin (θ / 2) • ((2 : ℝ) • lorJ8 rot4_1) := by
    unfold rotRotor8_1
    rw [neg_div, Real.cos_neg, Real.sin_neg, neg_smul, sub_eq_add_neg]
  have hK1_para := k1_para_lemma x₀ x₁
  have hK1_perp := k1_perp_lemma x₂ x₃
  have hK1_act : ((2 : ℝ) • lorK8 sigma4_1) * weylDirac8 x₀ x₁ 0 0 = weylDirac8 x₁ x₀ 0 0 := by
    have hCom := (weylDirac8_lorentz_equivariance_and_massive_casimir x₀ x₁ 0 0 0).2.2.2.1
    have hRight : weylDirac8 x₀ x₁ 0 0 * ((2 : ℝ) • lorK8 sigma4_1) =
        -(((2 : ℝ) • lorK8 sigma4_1) * weylDirac8 x₀ x₁ 0 0) := by
      rw [hK1_para, neg_neg]
    have hEq : ((2 : ℝ) • lorK8 sigma4_1) * weylDirac8 x₀ x₁ 0 0 -
        weylDirac8 x₀ x₁ 0 0 * ((2 : ℝ) • lorK8 sigma4_1) =
        (2 : ℝ) • weylDirac8 x₁ x₀ 0 0 := by
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hCom]
    rw [hRight, sub_neg_eq_add, ← two_smul ℝ] at hEq
    exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) hEq
  have hBoost1 : boostRotor8_1 t * weylDirac8 x₀ x₁ x₂ x₃ * boostRotor8_1 (-t) =
      weylDirac8 (Real.cosh t * x₀ + Real.sinh t * x₁) (Real.sinh t * x₀ + Real.cosh t * x₁) x₂ x₃ := by
    have hSplitD : weylDirac8 x₀ x₁ x₂ x₃ = weylDirac8 x₀ x₁ 0 0 + weylDirac8 0 0 x₂ x₃ := by
      rw [weylDirac8_linear_add]; simp only [add_zero, zero_add]
    rw [hSplitD, mul_add, add_mul, hB1_neg]
    unfold boostRotor8_1
    rw [invol_conj_anticomm hK1_sq hK1_para, invol_conj_comm hK1_sq hK1_perp,
      scalar_cosh_two_half, scalar_sinh_two_half, scalar_hyp_sq_diff, one_smul,
      hK1_act, weylDirac8_linear_smul, weylDirac8_linear_smul,
      weylDirac8_linear_add, weylDirac8_linear_add]
    simp only [mul_zero, add_zero, zero_add, add_comm (Real.cosh t * x₁)]
  have hK3_para := k3_para_lemma x₀ x₃
  have hK3_perp := k3_perp_lemma x₁ x₂
  have hK3_act : ((2 : ℝ) • lorK8 sigma4_3) * weylDirac8 x₀ 0 0 x₃ = weylDirac8 x₃ 0 0 x₀ := by
    have hCom := (weylDirac8_lorentz_equivariance_and_massive_casimir x₀ 0 0 x₃ 0).2.2.2.2.2.1
    have hRight : weylDirac8 x₀ 0 0 x₃ * ((2 : ℝ) • lorK8 sigma4_3) =
        -(((2 : ℝ) • lorK8 sigma4_3) * weylDirac8 x₀ 0 0 x₃) := by
      rw [hK3_para, neg_neg]
    have hEq : ((2 : ℝ) • lorK8 sigma4_3) * weylDirac8 x₀ 0 0 x₃ -
        weylDirac8 x₀ 0 0 x₃ * ((2 : ℝ) • lorK8 sigma4_3) = (2 : ℝ) • weylDirac8 x₃ 0 0 x₀ := by
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hCom]
    rw [hRight, sub_neg_eq_add, ← two_smul ℝ] at hEq
    exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) hEq
  have hBoost3 : boostRotor8_3 t * weylDirac8 x₀ x₁ x₂ x₃ * boostRotor8_3 (-t) =
      weylDirac8 (Real.cosh t * x₀ + Real.sinh t * x₃) x₁ x₂ (Real.sinh t * x₀ + Real.cosh t * x₃) := by
    have hSplitD : weylDirac8 x₀ x₁ x₂ x₃ = weylDirac8 x₀ 0 0 x₃ + weylDirac8 0 x₁ x₂ 0 := by
      rw [weylDirac8_linear_add]; simp only [add_zero, zero_add]
    rw [hSplitD, mul_add, add_mul, hB3_neg]
    unfold boostRotor8_3
    rw [invol_conj_anticomm hK3_sq hK3_para, invol_conj_comm hK3_sq hK3_perp,
      scalar_cosh_two_half, scalar_sinh_two_half, scalar_hyp_sq_diff, one_smul,
      hK3_act, weylDirac8_linear_smul, weylDirac8_linear_smul,
      weylDirac8_linear_add, weylDirac8_linear_add]
    simp only [mul_zero, add_zero, zero_add, add_comm (Real.cosh t * x₃)]
  have hJ1_para := j1_para_lemma x₂ x₃
  have hJ1_perp := j1_perp_lemma x₀ x₁
  have hJ1_act : ((2 : ℝ) • lorJ8 rot4_1) * weylDirac8 0 0 x₂ x₃ = weylDirac8 0 0 (-x₃) x₂ := by
    have hCom := (weylDirac8_lorentz_equivariance_and_massive_casimir 0 0 x₂ x₃ 0).1
    have hRight : weylDirac8 0 0 x₂ x₃ * ((2 : ℝ) • lorJ8 rot4_1) =
        -(((2 : ℝ) • lorJ8 rot4_1) * weylDirac8 0 0 x₂ x₃) := by
      rw [hJ1_para, neg_neg]
    have hEq : ((2 : ℝ) • lorJ8 rot4_1) * weylDirac8 0 0 x₂ x₃ -
        weylDirac8 0 0 x₂ x₃ * ((2 : ℝ) • lorJ8 rot4_1) = (2 : ℝ) • weylDirac8 0 0 (-x₃) x₂ := by
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hCom]
    rw [hRight, sub_neg_eq_add, ← two_smul ℝ] at hEq
    exact smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0) hEq
  have hRot1 : rotRotor8_1 θ * weylDirac8 x₀ x₁ x₂ x₃ * rotRotor8_1 (-θ) =
      weylDirac8 x₀ x₁ (Real.cos θ * x₂ - Real.sin θ * x₃) (Real.sin θ * x₂ + Real.cos θ * x₃) := by
    have hSplitD : weylDirac8 x₀ x₁ x₂ x₃ = weylDirac8 0 0 x₂ x₃ + weylDirac8 x₀ x₁ 0 0 := by
      rw [weylDirac8_linear_add]; simp only [add_zero, zero_add]
    rw [hSplitD, mul_add, add_mul, hR1_neg]
    unfold rotRotor8_1
    rw [skew_conj_anticomm hJ1_sq hJ1_para, skew_conj_comm hJ1_sq hJ1_perp,
      scalar_cos_two_half, scalar_sin_two_half, scalar_trig_sq_sum, one_smul,
      hJ1_act, weylDirac8_linear_smul, weylDirac8_linear_smul,
      weylDirac8_linear_add, weylDirac8_linear_add]
    simp only [mul_zero, add_zero, zero_add, sub_eq_add_neg, mul_neg,
      add_comm (Real.cos θ * x₃)]
  have hLB : InfoGeometry.LLM.KreinPositionalThermodynamicAttention.lorentzBoost2 η ⊗ₖ
      (1 : Matrix (Fin 4) (Fin 4) ℝ) =
      Real.cosh η • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + Real.sinh η • mirror8 := by
    rw [lorentzBoost2_eq_cosh_add_sinh_xMir2, Matrix.add_kronecker,
      Matrix.smul_kronecker, Matrix.smul_kronecker, Matrix.one_kronecker_one]
    rfl
  have hTM : ((1 / 2 : ℝ) • InfoGeometry.OperatorAlgebra.OsterwalderSchraderTransferSemigroupAndMassGap.transferMatHyp J) ⊗ₖ
      (1 : Matrix (Fin 4) (Fin 4) ℝ) =
      Real.cosh J • (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) + Real.sinh J • mirror8 := by
    rw [transferMatHyp_half_eq_cosh_add_sinh_xMir2, Matrix.add_kronecker,
      Matrix.smul_kronecker, Matrix.smul_kronecker, Matrix.one_kronecker_one]
    rfl
  exact ⟨hB1_mul t₁ t₂, hB1_inv, hB3_mul t₁ t₂, hB3_inv, hR1_mul θ₁ θ₂, hR1_inv,
    hBoost1, hBoost3, hRot1, hLB, hTM⟩

/-! ### Part 4: `k = 2 → k = 3` (`M₁₆(ℝ)`) Lift & Zorn `1 + 3 + 3 + 1` Lepton–Quark Color Split Capstone -/

/-- `M₁₆(ℝ)` (`Cl(4,4)` rung) embedding `I₂ ⊗ weylDirac8 x`. -/
def weylDirac16 (x₀ x₁ x₂ x₃ : ℝ) :
    Matrix (Fin 2 × (Fin 2 × Fin 4)) (Fin 2 × (Fin 2 × Fin 4)) ℝ :=
  (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ weylDirac8 x₀ x₁ x₂ x₃

/-- Outer `Cl(4,4)` chirality grading `Z ⊗ Γ₅` on `M₁₆(ℝ)`. -/
def chiralSplit16 :
    Matrix (Fin 2 × (Fin 2 × Fin 4)) (Fin 2 × (Fin 2 × Fin 4)) ℝ :=
  zCut2 ⊗ₖ gamma5_8

/-- Explicit non-commutativity witness in `Matrix (Fin 2 × (Fin 2 × Fin 4)) (Fin 2 × (Fin 2 × Fin 4)) ℝ`. -/
theorem exists_noncomm_mat2x8_pol :
    ∃ A B : Matrix (Fin 2 × (Fin 2 × Fin 4)) (Fin 2 × (Fin 2 × Fin 4)) ℝ, A * B ≠ B * A := by
  refine ⟨chiralSplit16, weylDirac16 1 0 0 0, fun h => ?_⟩
  have hU := unified_weyl_dirac8_and_susy_block 1 0 0 0 1 0 0 0 0 0 0 0
  have hAnti : chiralSplit16 * weylDirac16 1 0 0 0 + weylDirac16 1 0 0 0 * chiralSplit16 = 0 := by
    dsimp [chiralSplit16, weylDirac16]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
      ← Matrix.kronecker_add, hU.2.1, Matrix.kronecker_zero]
  have hTwo : (2 : ℝ) • (chiralSplit16 * weylDirac16 1 0 0 0) = 0 := by
    rw [two_smul]; conv_rhs => rw [← hAnti]
    rw [h]
  have hZero := (smul_eq_zero.mp hTwo).resolve_left (by norm_num)
  have hMul : (chiralSplit16 * weylDirac16 1 0 0 0) * weylDirac16 1 0 0 0 = 0 := by
    rw [hZero, zero_mul]
  have hW16Sq : weylDirac16 1 0 0 0 * weylDirac16 1 0 0 0 = 1 := by
    dsimp [weylDirac16]
    rw [← Matrix.mul_kronecker_mul, one_mul, hU.2.2.2.2.1]
    simp
  rw [Matrix.mul_assoc, hW16Sq, mul_one] at hMul
  have hDiag := congrArg
    (fun M : Matrix (Fin 2 × (Fin 2 × Fin 4)) (Fin 2 × (Fin 2 × Fin 4)) ℝ =>
      M (0, (0, 0)) (0, (0, 0))) hMul
  simp [chiralSplit16, gamma5_8, zCut2, pPlus2, pMinus2, Matrix.kroneckerMap_apply] at hDiag

/-- **Theorem 4 (Master Capstone: `k=2 → k=3` `M₁₆(ℝ)` Lift & Zorn `1 + 3 + 3 + 1` Lepton–Quark Color Split)**:
Synthesizes across existing repository owners:
1. `weylDirac16` Clifford interval `weylDirac16(x)² = (x₀² - x₁² - x₂² - x₃²) • I₁₆` and `chiralSplit16`
   anticommutation `{chiralSplit16, weylDirac16(x)} = 0` inside `M₁₆(ℝ)` (`Cl(4,4)` rung).
2. `SplitOctonion1331OperatorGradingBridge.zorn_1331_decomposition`: exact `1 + 3 + 3 + 1` Peirce
   splitting `Z = degreeZero Z + degreeOne Z + degreeTwo Z + degreeThree Z` on `ZornMatrix ℝ`.
3. `PauliWeylTwistorQuarkColor`: lepton singlet subalgebra (`isLeptonSinglet`), quark color
   nilpotency (`u_i² = 0`), diquark color cross product (`u₀ u₁ = u₂*`), and CAR relations
   (`{u_i, u_j*} = -δ_{ij} 1`).
4. `KleinianZornCl44Bridge`: Cayley–Dickson `octSToZorn` algebra equivalence and Kleinian
   rank-4 null-plane incidence (`finrank (ker (leftMulLinear z)) = 4`). -/
theorem weylDirac8_zorn_cl44_lepton_quark_color_capstone
    {R : Type*} [CommRing R]
    (x₀ x₁ x₂ x₃ : ℝ)
    (Z : InfoGeometry.Canonical.ZornMatrix ℝ)
    (X Y : InfoGeometry.Algebra.ZornVectorMatrix R)
    (hX : InfoGeometry.Canonical.PauliWeylTwistorQuarkColor.isLeptonSinglet X)
    (hY : InfoGeometry.Canonical.PauliWeylTwistorQuarkColor.isLeptonSinglet Y)
    (u v : InfoGeometry.Canonical.KleinianWittBornNullIncidence.OctS)
    (z : InfoGeometry.Canonical.ZornMatrix ℝ) (hz : z ≠ 0)
    (hnull : InfoGeometry.Canonical.ZornClifford.zornNormFun z = 0) :
    (weylDirac16 x₀ x₁ x₂ x₃ * weylDirac16 x₀ x₁ x₂ x₃ =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) •
        (1 : Matrix (Fin 2 × (Fin 2 × Fin 4)) (Fin 2 × (Fin 2 × Fin 4)) ℝ)) ∧
    (chiralSplit16 * weylDirac16 x₀ x₁ x₂ x₃ + weylDirac16 x₀ x₁ x₂ x₃ * chiralSplit16 = 0) ∧
    (Z = InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge.degreeZero Z +
      InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge.degreeOne Z +
      InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge.degreeTwo Z +
      InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge.degreeThree Z) ∧
    InfoGeometry.Canonical.PauliWeylTwistorQuarkColor.isLeptonSinglet
      (InfoGeometry.Algebra.ZornVectorMatrix.mul X Y) ∧
    (∀ i : Fin 3, InfoGeometry.Algebra.ZornVectorMatrix.mul
      (InfoGeometry.Canonical.GunaydinGursey.u i)
      (InfoGeometry.Canonical.GunaydinGursey.u i : InfoGeometry.Algebra.ZornVectorMatrix R) =
      InfoGeometry.Algebra.ZornVectorMatrix.zero) ∧
    (InfoGeometry.Algebra.ZornVectorMatrix.mul
      (InfoGeometry.Canonical.GunaydinGursey.u 0 : InfoGeometry.Algebra.ZornVectorMatrix R)
      (InfoGeometry.Canonical.GunaydinGursey.u 1) =
      InfoGeometry.Canonical.GunaydinGursey.uStar 2) ∧
    (InfoGeometry.Canonical.KleinianZornCl44Bridge.octSToZorn
        (InfoGeometry.Canonical.KleinianWittBornNullIncidence.octMul u v) =
      InfoGeometry.Canonical.KleinianZornCl44Bridge.octSToZorn u *
        InfoGeometry.Canonical.KleinianZornCl44Bridge.octSToZorn v) ∧
    (Module.finrank ℝ (LinearMap.ker
      (InfoGeometry.Canonical.ZornMatrix.leftMulLinear z)) = 4) := by
  have hU := unified_weyl_dirac8_and_susy_block x₀ x₁ x₂ x₃ x₀ x₁ x₂ x₃ 0 0 0 0
  have hW8Sq : weylDirac8 x₀ x₁ x₂ x₃ * weylDirac8 x₀ x₁ x₂ x₃ =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) •
        (1 : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℝ) := hU.2.2.2.2.1
  have hW16Sq : weylDirac16 x₀ x₁ x₂ x₃ * weylDirac16 x₀ x₁ x₂ x₃ =
      (x₀ ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2) •
        (1 : Matrix (Fin 2 × (Fin 2 × Fin 4)) (Fin 2 × (Fin 2 × Fin 4)) ℝ) := by
    dsimp [weylDirac16]
    rw [← Matrix.mul_kronecker_mul, one_mul, hW8Sq, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  have hChiral : chiralSplit16 * weylDirac16 x₀ x₁ x₂ x₃ +
      weylDirac16 x₀ x₁ x₂ x₃ * chiralSplit16 = 0 := by
    dsimp [chiralSplit16, weylDirac16]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, mul_one, one_mul,
      ← Matrix.kronecker_add, hU.2.1, Matrix.kronecker_zero]
  exact ⟨hW16Sq, hChiral,
    InfoGeometry.Lie.SplitOctonion1331OperatorGradingBridge.zorn_1331_decomposition Z,
    (InfoGeometry.Canonical.PauliWeylTwistorQuarkColor.lepton_singlet_subalgebra X Y hX hY).1,
    InfoGeometry.Canonical.PauliWeylTwistorQuarkColor.quark_color_nilpotent,
    InfoGeometry.Canonical.PauliWeylTwistorQuarkColor.diquark_color_01,
    InfoGeometry.Canonical.KleinianZornCl44Bridge.octSToZorn_mul u v,
    InfoGeometry.Canonical.KleinianZornCl44Bridge.zorn_null_ker_finrank_four z hz hnull⟩

end InfoGeometry.Canonical.PolarizedWeylDiracLorentzColorBridge
