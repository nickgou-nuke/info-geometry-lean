/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
import InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
import InfoGeometry.Clifford.LochakRodichevFierzKrein
import InfoGeometry.OperatorAlgebra.PeirceSpine.AlternatingCornerTriple
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# The Road to Gravity from Spinning: Graded Cartan Curvature, Torsion, & Real Palatini Trace

Formalizes the passage from local spinning connections to Einstein–Cartan / MacDowell–Mansouri
Palatini gravity strictly over `ℝ` (`0` complex `i`), reusing committed owners
`DoubledMinkowskiBdGColimitBridge`, `DoubledMinkowskiRotatingSpinInstability`,
`DiracSpinCasimirNambuModulesBridge`, and `PeirceSpine.comm`:

1. **Universal Graded Cartan–MacDowell–Mansouri Split (`cartan_curvature_torsion_graded_split`)**:
   In any associative ring `B` with chiral involution/parity operator `Γ`, decomposing
   `𝒜_i = ω_i + e_i` splits total curvature `ℱ₁₂ = (dω + de) + [𝒜₁, 𝒜₂]` into `Γ`-even
   `(R₁₂ + [e₁, e₂])` (Riemann curvature + area bivector) and `Γ`-odd `T₁₂` (Cartan torsion),
   together with general `Γ`-odd trace annihilation (`graded_odd_trace_zero`).
2. **Real `M₄(ℝ)` Majorana–Dirac Realization (`soldering_commutators_generate_spin_and_palatini_gravity`)**:
   Uses the repository-verified Clifford generators `diracGamma0..3` and volume element
   `diracOmega4 = γ₀ γ₁ γ₂ γ₃` (repairing the off-diagonal block position of `gamma0_fin4` relative
   to `diracGamma0 = eps2 ⊗ₖ 1`, where placing `eps2` in the inner factor `1 ⊗ₖ eps2` would
   wrongly commute with `γ₃ = zCut2 ⊗ₖ 1`). Proves:
   - `{diracOmega4, solderVec a} = 0` and `[diracOmega4, spinBiv a b] = 0`,
   - Vanishing even–odd torsion cross-trace `Tr(diracOmega4 * spinBiv a b * solderVec c) = 0`,
   - Exact Hodge-dual Palatini contractions `Tr(diracOmega4 * spinBiv a b * [e_c, e_d]) = -ε_{abcd}`
     (`-1` on complementary planes `(0,1,2,3)`, `(0,2,3,1)`, `(0,3,1,2)`, and `0` on repeated/shared
     planes `(0,1,0,1)` and `(0,1,1,2)`).

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE THEOREMS
* `diracGamma0_reindex_eq_gamma0_fin4`
* `soldering_commutators_generate_spin_and_palatini_gravity`
* `palatini_trace_eq_neg_leviCivita4`
* `macdowell_mansouri_action_expansion`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `cartan_curvature_torsion_graded_split` (under explicit `Γ`-even `ω`, `Γ`-odd `e` hypotheses)
* `graded_odd_trace_zero` (under explicit `Γ * Γ = -1` and `Γ * X = -(X * Γ)`)

#### BUCKET 3: OPEN CLOSURE DEBT
* Smooth manifold differential-form wedge integration (`∫_M Tr(γ₅ ℱ ∧ ℱ)`) over a 4D spin
  bundle remains outside this finite pointwise Clifford-algebra bridge.
-/

noncomputable section

open scoped BigOperators Kronecker
open Matrix

namespace InfoGeometry.Canonical.RoadToGravityFromSpinning

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### Part 1: Universal Graded Cartan–MacDowell–Mansouri Curvature & Torsion Split -/

private lemma scalar_eq_zero_of_eq_neg {x : ℝ} (h : x = -x) : x = 0 := by
  linarith [h]

/-- **Theorem 1 (Universal Cartan Connection Split into Riemann Curvature, Area Bivector, & Torsion)**:
Reusing `PeirceSpine.comm`, for any `Γ`-even spin connection data (`ω₁, ω₂, dω`) and `Γ`-odd
soldering tetrad data (`e₁, e₂, de`), total curvature splits cleanly into `Γ`-even `(R₁₂ + E₁₂)`
and `Γ`-odd `T₁₂`, with exact MacDowell–Mansouri quadratic expansion. -/
theorem cartan_curvature_torsion_graded_split {B : Type*} [Ring B]
    (Γ ω₁ ω₂ dω e₁ e₂ de : B)
    (hω1 : Γ * ω₁ = ω₁ * Γ) (hω2 : Γ * ω₂ = ω₂ * Γ) (hdω : Γ * dω = dω * Γ)
    (he1 : Γ * e₁ = -(e₁ * Γ)) (he2 : Γ * e₂ = -(e₂ * Γ)) (hde : Γ * de = -(de * Γ)) :
    let A₁ := ω₁ + e₁
    let A₂ := ω₂ + e₂
    let F₁₂ := (dω + de) + PeirceSpine.comm A₁ A₂
    let R₁₂ := dω + PeirceSpine.comm ω₁ ω₂
    let E₁₂ := PeirceSpine.comm e₁ e₂
    let T₁₂ := de + PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁
    (F₁₂ = (R₁₂ + E₁₂) + T₁₂) ∧
    (Γ * (R₁₂ + E₁₂) = (R₁₂ + E₁₂) * Γ) ∧
    (Γ * T₁₂ = -(T₁₂ * Γ)) ∧
    ((R₁₂ + E₁₂) * (R₁₂ + E₁₂) =
      R₁₂ * R₁₂ + (R₁₂ * E₁₂ + E₁₂ * R₁₂) + E₁₂ * E₁₂) := by
  dsimp [PeirceSpine.comm]
  have hG_w1w2 : Γ * (ω₁ * ω₂) = (ω₁ * ω₂) * Γ := by
    calc Γ * (ω₁ * ω₂) = (Γ * ω₁) * ω₂ := by noncomm_ring
      _ = ω₁ * (Γ * ω₂) := by rw [hω1]; noncomm_ring
      _ = (ω₁ * ω₂) * Γ := by rw [hω2]; noncomm_ring
  have hG_w2w1 : Γ * (ω₂ * ω₁) = (ω₂ * ω₁) * Γ := by
    calc Γ * (ω₂ * ω₁) = (Γ * ω₂) * ω₁ := by noncomm_ring
      _ = ω₂ * (Γ * ω₁) := by rw [hω2]; noncomm_ring
      _ = (ω₂ * ω₁) * Γ := by rw [hω1]; noncomm_ring
  have hG_e1e2 : Γ * (e₁ * e₂) = (e₁ * e₂) * Γ := by
    calc Γ * (e₁ * e₂) = (Γ * e₁) * e₂ := by noncomm_ring
      _ = -(e₁ * (Γ * e₂)) := by rw [he1]; noncomm_ring
      _ = (e₁ * e₂) * Γ := by rw [he2]; noncomm_ring
  have hG_e2e1 : Γ * (e₂ * e₁) = (e₂ * e₁) * Γ := by
    calc Γ * (e₂ * e₁) = (Γ * e₂) * e₁ := by noncomm_ring
      _ = -(e₂ * (Γ * e₁)) := by rw [he2]; noncomm_ring
      _ = (e₂ * e₁) * Γ := by rw [he1]; noncomm_ring
  have hG_w1e2 : Γ * (ω₁ * e₂) = -(ω₁ * e₂ * Γ) := by
    calc Γ * (ω₁ * e₂) = (Γ * ω₁) * e₂ := by noncomm_ring
      _ = ω₁ * (Γ * e₂) := by rw [hω1]; noncomm_ring
      _ = -(ω₁ * e₂ * Γ) := by rw [he2]; noncomm_ring
  have hG_e2w1 : Γ * (e₂ * ω₁) = -(e₂ * ω₁ * Γ) := by
    calc Γ * (e₂ * ω₁) = (Γ * e₂) * ω₁ := by noncomm_ring
      _ = -(e₂ * (Γ * ω₁)) := by rw [he2]; noncomm_ring
      _ = -(e₂ * ω₁ * Γ) := by rw [hω1]; noncomm_ring
  have hG_w2e1 : Γ * (ω₂ * e₁) = -(ω₂ * e₁ * Γ) := by
    calc Γ * (ω₂ * e₁) = (Γ * ω₂) * e₁ := by noncomm_ring
      _ = ω₂ * (Γ * e₁) := by rw [hω2]; noncomm_ring
      _ = -(ω₂ * e₁ * Γ) := by rw [he1]; noncomm_ring
  have hG_e1w2 : Γ * (e₁ * ω₂) = -(e₁ * ω₂ * Γ) := by
    calc Γ * (e₁ * ω₂) = (Γ * e₁) * ω₂ := by noncomm_ring
      _ = -(e₁ * (Γ * ω₂)) := by rw [he1]; noncomm_ring
      _ = -(e₁ * ω₂ * Γ) := by rw [hω2]; noncomm_ring
  refine ⟨by noncomm_ring, ?_, ?_, by noncomm_ring⟩
  · calc Γ * (dω + (ω₁ * ω₂ - ω₂ * ω₁) + (e₁ * e₂ - e₂ * e₁))
        = Γ * dω + (Γ * (ω₁ * ω₂) - Γ * (ω₂ * ω₁)) + (Γ * (e₁ * e₂) - Γ * (e₂ * e₁)) := by
            noncomm_ring
      _ = (dω + (ω₁ * ω₂ - ω₂ * ω₁) + (e₁ * e₂ - e₂ * e₁)) * Γ := by
            rw [hdω, hG_w1w2, hG_w2w1, hG_e1e2, hG_e2e1]; noncomm_ring
  · calc Γ * (de + (ω₁ * e₂ - e₂ * ω₁) - (ω₂ * e₁ - e₁ * ω₂))
        = Γ * de + (Γ * (ω₁ * e₂) - Γ * (e₂ * ω₁)) - (Γ * (ω₂ * e₁) - Γ * (e₁ * ω₂)) := by
            noncomm_ring
      _ = -((de + (ω₁ * e₂ - e₂ * ω₁) - (ω₂ * e₁ - e₁ * ω₂)) * Γ) := by
            rw [hde, hG_w1e2, hG_e2w1, hG_w2e1, hG_e1w2]; noncomm_ring

/-- Any finite real matrix `X` that is odd under a square-`-1` operator `Γ` (`Γ * Γ = -1` and
`Γ * X = -(X * Γ)`) has vanishing trace (`Tr(X) = 0`), killing all even–odd torsion cross-terms. -/
theorem graded_odd_trace_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ X : Matrix ι ι ℝ) (hSq : Γ * Γ = -1) (hOdd : Γ * X = -(X * Γ)) :
    Matrix.trace X = 0 := by
  have hTr : Matrix.trace X = -Matrix.trace X := by
    calc
      Matrix.trace X = -Matrix.trace ((-1 : Matrix ι ι ℝ) * X) := by
        rw [Matrix.neg_mul, Matrix.one_mul, Matrix.trace_neg, neg_neg]
      _ = -Matrix.trace (Γ * Γ * X) := by rw [hSq]
      _ = -Matrix.trace (Γ * (Γ * X)) := by simp only [Matrix.mul_assoc]
      _ = -Matrix.trace ((Γ * X) * Γ) := by rw [Matrix.trace_mul_comm]
      _ = -Matrix.trace (-(X * Γ) * Γ) := by rw [hOdd]
      _ = Matrix.trace (X * (Γ * Γ)) := by
        rw [Matrix.neg_mul, Matrix.trace_neg, neg_neg, Matrix.mul_assoc]
      _ = Matrix.trace (X * (-1 : Matrix ι ι ℝ)) := by rw [hSq]
      _ = -Matrix.trace X := by rw [Matrix.mul_neg, Matrix.mul_one, Matrix.trace_neg]
  exact scalar_eq_zero_of_eq_neg hTr

/-! ### Part 2: Concrete 4D Real Majorana–Dirac Cl(3,1) ≅ M₄(ℝ) Realization of Palatini Gravity -/

/-- Repaired explicit `Fin 4 × Fin 4` Majorana matrix for `diracGamma0 = eps2 ⊗ₖ 1`
(putting `eps2` in the outer block so `{γ₀, γ₃} = 0` holds, unlike `1 ⊗ₖ eps2`). -/
def gamma0_fin4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0,  0, 1, 0;
      0,  0, 0, 1;
     -1,  0, 0, 0;
      0, -1, 0, 0]

/-- Reindexing `DiracSpinCasimirNambuModulesBridge.diracGamma0` yields `gamma0_fin4`. -/
theorem diracGamma0_reindex_eq_gamma0_fin4 :
    Matrix.reindex finProdFinEquiv finProdFinEquiv diracGamma0 = gamma0_fin4 := by
  have hs0 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 0 = (0, 0) := by decide
  have hs1 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 1 = (0, 1) := by decide
  have hs2 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 2 = (1, 0) := by decide
  have hs3 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 3 = (1, 1) := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, hs0, hs1, hs2, hs3, diracGamma0, gamma0_fin4,
      Matrix.kroneckerMap_apply, eps2]

/-- Soldering translation generators `e_a = ½ γ_a` on `Fin 2 × Fin 2` using the verified
repository generators `diracGamma0..3`. -/
def solderVec : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ
  | 0 => (1 / 2 : ℝ) • diracGamma0
  | 1 => (1 / 2 : ℝ) • diracGamma1
  | 2 => (1 / 2 : ℝ) • diracGamma2
  | 3 => (1 / 2 : ℝ) • diracGamma3

/-- Lorentz spin bivector generators `Σ_{ab} = [e_a, e_b] = ¼[γ_a, γ_b] ∈ so(1,3)`. -/
def spinBiv (a b : Fin 4) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  PeirceSpine.comm (solderVec a) (solderVec b)

private lemma pauli2_kron_rules :
    (zCut2 * zCut2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (xMir2 * xMir2 = (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (eps2 * eps2 = -(1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (zCut2 * xMir2 = eps2) ∧ (xMir2 * zCut2 = -eps2) ∧
    (zCut2 * eps2 = xMir2) ∧ (eps2 * zCut2 = -xMir2) ∧
    (xMir2 * eps2 = -zCut2) ∧ (eps2 * xMir2 = zCut2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { ext i j; fin_cases i <;> fin_cases j <;>
        simp [zCut2, xMir2, eps2, Matrix.mul_apply, Fin.sum_univ_two] }

private lemma kron_neg_left' {m₁ n₁ m₂ n₂ : Type*}
    (A : Matrix m₁ n₁ ℝ) (B : Matrix m₂ n₂ ℝ) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kron_neg_right' {m₁ n₁ m₂ n₂ : Type*}
    (A : Matrix m₁ n₁ ℝ) (B : Matrix m₂ n₂ ℝ) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma diracOmega4_eq_kron : diracOmega4 = -(xMir2 ⊗ₖ eps2) := by
  obtain ⟨_, _, _, hZX, hXZ, hZE, _, _, hEX⟩ := pauli2_kron_rules
  unfold diracOmega4 diracGamma0 diracGamma1 diracGamma2 diracGamma3
  rw [mul_assoc, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    hEX, Matrix.one_mul, hXZ, Matrix.mul_one,
    ← Matrix.mul_kronecker_mul, Matrix.mul_neg, hZE, hZX, kron_neg_left']

private lemma diracOmega4_anticomm_diracGamma :
    (diracOmega4 * diracGamma0 + diracGamma0 * diracOmega4 = 0) ∧
    (diracOmega4 * diracGamma1 + diracGamma1 * diracOmega4 = 0) ∧
    (diracOmega4 * diracGamma2 + diracGamma2 * diracOmega4 = 0) ∧
    (diracOmega4 * diracGamma3 + diracGamma3 * diracOmega4 = 0) := by
  obtain ⟨_, hXX, _, hZX, hXZ, hZE, hEZ, hXE, hEX⟩ := pauli2_kron_rules
  rw [diracOmega4_eq_kron]
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [diracGamma0]
    rw [neg_mul, mul_neg, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, hXE, hEX, kron_neg_left', neg_neg, add_neg_cancel]
  · dsimp [diracGamma1]
    rw [neg_mul, mul_neg, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hXX, hEZ, hZE, kron_neg_right', neg_neg, add_neg_cancel]
  · dsimp [diracGamma2]
    rw [neg_mul, mul_neg, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      hXX, hEX, hXE, kron_neg_right', neg_neg, neg_add_cancel]
  · dsimp [diracGamma3]
    rw [neg_mul, mul_neg, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, hXZ, hZX, kron_neg_left', neg_neg, add_neg_cancel]

private lemma spinBiv_eq_half_prod {a b : Fin 4} {G₁ G₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ}
    (hs1 : solderVec a = (1 / 2 : ℝ) • G₁) (hs2 : solderVec b = (1 / 2 : ℝ) • G₂)
    (hAnti : G₁ * G₂ + G₂ * G₁ = 0) :
    spinBiv a b = (1 / 2 : ℝ) • (G₁ * G₂) := by
  unfold spinBiv PeirceSpine.comm
  rw [hs1, hs2, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, eq_neg_of_add_eq_zero_right hAnti]
  module

private lemma palatini_trace_neg_one (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (hX : X = (1 / 4 : ℝ) • (diracOmega4 * diracOmega4)) :
    Matrix.trace X = -1 := by
  rw [hX, lorentz_spin_algebra_and_two_casimirs.2.2.2.2.2.1, Matrix.trace_smul,
    Matrix.trace_neg, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin]
  norm_num

/-- **Theorem 2 (The Road from Spinning to Einstein–Hilbert–Palatini Gravity in Real `M₄(ℝ)`)**:
1. `{diracOmega4, solderVec a} = 0` and `[diracOmega4, spinBiv a b] = 0`.
2. Vanishing even–odd torsion cross-trace `Tr(diracOmega4 * spinBiv a b * solderVec c) = 0`.
3. Exact Hodge-dual Palatini contractions `Tr(diracOmega4 * spinBiv a b * [e_c, e_d]) = -ε_{abcd}`:
   `-1` on `(0,1,2,3)`, `(0,2,3,1)`, `(0,3,1,2)`, and `0` on `(0,1,0,1)` and `(0,1,1,2)`. -/
theorem soldering_commutators_generate_spin_and_palatini_gravity
    (a b c : Fin 4) :
    (diracOmega4 * solderVec a + solderVec a * diracOmega4 = 0) ∧
    (diracOmega4 * spinBiv a b = spinBiv a b * diracOmega4) ∧
    (Matrix.trace (diracOmega4 * spinBiv a b * solderVec c) = 0) ∧
    (Matrix.trace (diracOmega4 * spinBiv 0 1 * PeirceSpine.comm (solderVec 2) (solderVec 3)) = -1) ∧
    (Matrix.trace (diracOmega4 * spinBiv 0 2 * PeirceSpine.comm (solderVec 3) (solderVec 1)) = -1) ∧
    (Matrix.trace (diracOmega4 * spinBiv 0 3 * PeirceSpine.comm (solderVec 1) (solderVec 2)) = -1) ∧
    (Matrix.trace (diracOmega4 * spinBiv 0 1 * PeirceSpine.comm (solderVec 0) (solderVec 1)) = 0) ∧
    (Matrix.trace (diracOmega4 * spinBiv 0 1 * PeirceSpine.comm (solderVec 1) (solderVec 2)) = 0) := by
  have hOmA := diracOmega4_anticomm_diracGamma
  have hAnti : ∀ x : Fin 4, diracOmega4 * solderVec x + solderVec x * diracOmega4 = 0 := by
    intro x
    fin_cases x <;> dsimp [solderVec] <;> rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
    · rw [hOmA.1, smul_zero]
    · rw [hOmA.2.1, smul_zero]
    · rw [hOmA.2.2.1, smul_zero]
    · rw [hOmA.2.2.2, smul_zero]
  have hComm : ∀ x y : Fin 4, diracOmega4 * spinBiv x y = spinBiv x y * diracOmega4 := by
    intro x y
    have hCommProd : ∀ u v : Fin 4,
        diracOmega4 * (solderVec u * solderVec v) = (solderVec u * solderVec v) * diracOmega4 := by
      intro u v
      have hu : diracOmega4 * solderVec u = -(solderVec u * diracOmega4) :=
        eq_neg_of_add_eq_zero_left (hAnti u)
      have hv : diracOmega4 * solderVec v = -(solderVec v * diracOmega4) :=
        eq_neg_of_add_eq_zero_left (hAnti v)
      calc
        diracOmega4 * (solderVec u * solderVec v)
            = (diracOmega4 * solderVec u) * solderVec v := by noncomm_ring
        _ = -(solderVec u * diracOmega4) * solderVec v := by rw [hu]
        _ = -(solderVec u * (diracOmega4 * solderVec v)) := by noncomm_ring
        _ = -(solderVec u * (-(solderVec v * diracOmega4))) := by rw [hv]
        _ = (solderVec u * solderVec v) * diracOmega4 := by noncomm_ring
    unfold spinBiv PeirceSpine.comm
    rw [mul_sub, sub_mul, hCommProd x y, hCommProd y x]
  have hOddTr : Matrix.trace (diracOmega4 * spinBiv a b * solderVec c) = 0 := by
    have hOdd : diracOmega4 * (diracOmega4 * spinBiv a b * solderVec c) =
        -((diracOmega4 * spinBiv a b * solderVec c) * diracOmega4) := by
      have hc : diracOmega4 * solderVec c = -(solderVec c * diracOmega4) :=
        eq_neg_of_add_eq_zero_left (hAnti c)
      calc
        diracOmega4 * (diracOmega4 * spinBiv a b * solderVec c)
            = diracOmega4 * ((diracOmega4 * spinBiv a b) * solderVec c) := by noncomm_ring
        _ = diracOmega4 * ((spinBiv a b * diracOmega4) * solderVec c) := by rw [hComm a b]
        _ = diracOmega4 * spinBiv a b * (diracOmega4 * solderVec c) := by noncomm_ring
        _ = -((diracOmega4 * spinBiv a b * solderVec c) * diracOmega4) := by
              rw [hc]; noncomm_ring
    exact graded_odd_trace_zero diracOmega4 _
      lorentz_spin_algebra_and_two_casimirs.2.2.2.2.2.1 hOdd
  obtain ⟨_, _, _, _, h01, h02, h03, h12, h13, h23⟩ := diracGamma_clifford_relations
  have h21 : diracGamma2 * diracGamma1 = -(diracGamma1 * diracGamma2) :=
    eq_neg_of_add_eq_zero_right h12
  have h31 : diracGamma3 * diracGamma1 = -(diracGamma1 * diracGamma3) :=
    eq_neg_of_add_eq_zero_right h13
  have h32 : diracGamma3 * diracGamma2 = -(diracGamma2 * diracGamma3) :=
    eq_neg_of_add_eq_zero_right h23
  have hs01 := spinBiv_eq_half_prod (a := 0) (b := 1) rfl rfl h01
  have hs23 := spinBiv_eq_half_prod (a := 2) (b := 3) rfl rfl h23
  have hs02 := spinBiv_eq_half_prod (a := 0) (b := 2) rfl rfl h02
  have hs31 := spinBiv_eq_half_prod (a := 3) (b := 1) rfl rfl
    (add_comm (diracGamma1 * diracGamma3) (diracGamma3 * diracGamma1) ▸ h13)
  have hs03 := spinBiv_eq_half_prod (a := 0) (b := 3) rfl rfl h03
  have hs12 := spinBiv_eq_half_prod (a := 1) (b := 2) rfl rfl h12
  obtain ⟨hZZ, hXX, _, hZX, hXZ, hZE, _, hXE, hEX⟩ := pauli2_kron_rules
  refine ⟨hAnti a, hComm a b, hOddTr, ?_, ?_, ?_, ?_, ?_⟩
  · apply palatini_trace_neg_one
    change diracOmega4 * spinBiv 0 1 * spinBiv 2 3 = _
    rw [hs01, hs23]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    norm_num [diracOmega4, mul_assoc]
  · apply palatini_trace_neg_one
    change diracOmega4 * spinBiv 0 2 * spinBiv 3 1 = _
    rw [hs02, hs31]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have hPerm : diracGamma0 * diracGamma2 * (diracGamma3 * diracGamma1) = diracOmega4 := by
      calc
        diracGamma0 * diracGamma2 * (diracGamma3 * diracGamma1)
            = diracGamma0 * diracGamma2 * (-(diracGamma1 * diracGamma3)) := by rw [h31]
        _ = -(diracGamma0 * (diracGamma2 * diracGamma1) * diracGamma3) := by noncomm_ring
        _ = -(diracGamma0 * (-(diracGamma1 * diracGamma2)) * diracGamma3) := by rw [h21]
        _ = diracGamma0 * diracGamma1 * diracGamma2 * diracGamma3 := by noncomm_ring
        _ = diracOmega4 := by rw [diracOmega4]
    rw [mul_assoc, hPerm]
    norm_num
  · apply palatini_trace_neg_one
    change diracOmega4 * spinBiv 0 3 * spinBiv 1 2 = _
    rw [hs03, hs12]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have hPerm : diracGamma0 * diracGamma3 * (diracGamma1 * diracGamma2) = diracOmega4 := by
      calc
        diracGamma0 * diracGamma3 * (diracGamma1 * diracGamma2)
            = diracGamma0 * (diracGamma3 * diracGamma1) * diracGamma2 := by noncomm_ring
        _ = diracGamma0 * (-(diracGamma1 * diracGamma3)) * diracGamma2 := by rw [h31]
        _ = -(diracGamma0 * diracGamma1 * (diracGamma3 * diracGamma2)) := by noncomm_ring
        _ = -(diracGamma0 * diracGamma1 * (-(diracGamma2 * diracGamma3))) := by rw [h32]
        _ = diracGamma0 * diracGamma1 * diracGamma2 * diracGamma3 := by noncomm_ring
        _ = diracOmega4 := by rw [diracOmega4]
    rw [mul_assoc, hPerm]
    norm_num
  · change Matrix.trace (diracOmega4 * spinBiv 0 1 * spinBiv 0 1) = 0
    have hProd : spinBiv 0 1 * spinBiv 0 1 = (1 / 4 : ℝ) • 1 := by
      rw [hs01, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have h01k : diracGamma0 * diracGamma1 = zCut2 ⊗ₖ zCut2 := by
        unfold diracGamma0 diracGamma1
        rw [← Matrix.mul_kronecker_mul, hEX, Matrix.one_mul]
      have hSq : (diracGamma0 * diracGamma1) * (diracGamma0 * diracGamma1) = 1 := by
        rw [h01k, ← Matrix.mul_kronecker_mul, hZZ, Matrix.one_kronecker_one]
      rw [hSq]
      norm_num
    rw [Matrix.mul_assoc, hProd, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
    have hTrOm : Matrix.trace diracOmega4 = 0 := by
      rw [diracOmega4_eq_kron, Matrix.trace_neg]
      simp [xMir2, eps2, Matrix.trace, Matrix.diag, Matrix.kroneckerMap_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hTrOm, smul_zero]
  · change Matrix.trace (diracOmega4 * spinBiv 0 1 * spinBiv 1 2) = 0
    have hProd : spinBiv 0 1 * spinBiv 1 2 = (1 / 4 : ℝ) • (diracGamma0 * diracGamma2) := by
      rw [hs01, hs12, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have h01k : diracGamma0 * diracGamma1 = zCut2 ⊗ₖ zCut2 := by
        unfold diracGamma0 diracGamma1
        rw [← Matrix.mul_kronecker_mul, hEX, Matrix.one_mul]
      have h12k : diracGamma1 * diracGamma2 = (1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ eps2 := by
        unfold diracGamma1 diracGamma2
        rw [← Matrix.mul_kronecker_mul, hXX, hZX]
      have h02k : diracGamma0 * diracGamma2 = zCut2 ⊗ₖ xMir2 := by
        unfold diracGamma0 diracGamma2
        rw [← Matrix.mul_kronecker_mul, hEX, Matrix.one_mul]
      have hM : (diracGamma0 * diracGamma1) * (diracGamma1 * diracGamma2) =
          diracGamma0 * diracGamma2 := by
        rw [h01k, h12k, h02k, ← Matrix.mul_kronecker_mul, Matrix.mul_one, hZE]
      rw [hM]
      norm_num
    rw [Matrix.mul_assoc, hProd, Matrix.mul_smul, Matrix.trace_smul]
    have hTr : Matrix.trace (diracOmega4 * (diracGamma0 * diracGamma2)) = 0 := by
      have hOm : diracOmega4 * (diracGamma0 * diracGamma2) = eps2 ⊗ₖ zCut2 := by
        rw [diracOmega4_eq_kron]
        have h02k : diracGamma0 * diracGamma2 = zCut2 ⊗ₖ xMir2 := by
          unfold diracGamma0 diracGamma2
          rw [← Matrix.mul_kronecker_mul, hEX, Matrix.one_mul]
        rw [h02k, neg_mul, ← Matrix.mul_kronecker_mul, hXZ, hEX,
          kron_neg_left', neg_neg]
      rw [hOm]
      simp [eps2, zCut2, Matrix.trace, Matrix.diag, Matrix.kroneckerMap_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hTr, smul_zero]

/-! ### Part 3: Universal 4D Levi-Civita Palatini Contraction & MacDowell–Mansouri Action Terms -/

private def id2Z : Matrix (Fin 2) (Fin 2) ℤ := 1
private def zCut2Z : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]
private def xMir2Z : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
private def eps2Z : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

private def gammaZ4 : Fin 4 → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ
  | 0 => eps2Z ⊗ₖ id2Z
  | 1 => xMir2Z ⊗ₖ zCut2Z
  | 2 => xMir2Z ⊗ₖ xMir2Z
  | 3 => zCut2Z ⊗ₖ id2Z

private def omegaZ4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ :=
  gammaZ4 0 * gammaZ4 1 * gammaZ4 2 * gammaZ4 3

private def commZ4 (a b : Fin 4) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ :=
  gammaZ4 a * gammaZ4 b - gammaZ4 b * gammaZ4 a

private def cast4 (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  (Int.castRingHom ℝ).mapMatrix M

private lemma cast4_mul (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ) :
    cast4 (A * B) = cast4 A * cast4 B :=
  (Int.castRingHom ℝ).mapMatrix.map_mul A B

private lemma cast4_sub (A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ) :
    cast4 (A - B) = cast4 A - cast4 B :=
  (Int.castRingHom ℝ).mapMatrix.map_sub A B

private lemma cast4_trace (A : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ) :
    Matrix.trace (cast4 A) = ((Matrix.trace A : ℤ) : ℝ) := by
  simp [cast4, Matrix.trace, Matrix.diag]

private lemma cast4_gamma0 : cast4 (gammaZ4 0) = diracGamma0 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4, gammaZ4, diracGamma0, eps2Z, id2Z, eps2, Matrix.kroneckerMap_apply]

private lemma cast4_gamma1 : cast4 (gammaZ4 1) = diracGamma1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4, gammaZ4, diracGamma1, xMir2Z, zCut2Z, xMir2, zCut2, Matrix.kroneckerMap_apply]

private lemma cast4_gamma2 : cast4 (gammaZ4 2) = diracGamma2 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4, gammaZ4, diracGamma2, xMir2Z, xMir2, Matrix.kroneckerMap_apply]

private lemma cast4_gamma3 : cast4 (gammaZ4 3) = diracGamma3 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [cast4, gammaZ4, diracGamma3, zCut2Z, id2Z, zCut2, Matrix.kroneckerMap_apply]

private lemma solderVec_eq_half_cast4 (a : Fin 4) :
    solderVec a = (1 / 2 : ℝ) • cast4 (gammaZ4 a) := by
  fin_cases a
  · simp [solderVec, cast4_gamma0]
  · simp [solderVec, cast4_gamma1]
  · simp [solderVec, cast4_gamma2]
  · simp [solderVec, cast4_gamma3]

private lemma diracOmega4_eq_cast4 : diracOmega4 = cast4 omegaZ4 := by
  unfold diracOmega4 omegaZ4
  rw [cast4_mul, cast4_mul, cast4_mul, cast4_gamma0, cast4_gamma1, cast4_gamma2, cast4_gamma3]

private lemma spinBiv_eq_quarter_cast4 (a b : Fin 4) :
    spinBiv a b = (1 / 4 : ℝ) • cast4 (commZ4 a b) := by
  unfold spinBiv PeirceSpine.comm commZ4
  rw [solderVec_eq_half_cast4 a, solderVec_eq_half_cast4 b,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul,
    ← smul_sub, ← cast4_mul, ← cast4_mul, ← cast4_sub]
  norm_num

private lemma palatini_trace_Z (a b c d : Fin 4) :
    Matrix.trace (omegaZ4 * commZ4 a b * commZ4 c d) =
      -16 * InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d := by
  revert a b c d
  decide

private lemma palatini_scalar_sixteenth (z : ℤ) :
    ((1 / 4 : ℝ) * (1 / 4 : ℝ)) * ((-16 * z : ℤ) : ℝ) = -(z : ℝ) := by
  push_cast
  ring

/-- **Theorem 3 (Universal 4D Hodge–Palatini Contraction)**:
For ALL indices `a b c d : Fin 4`,
`Tr(ω₄ Σ_{ab} [e_c, e_d]) = -ε_{abcd}` using `LochakRodichevFierzKrein.leviCivita4`. -/
theorem palatini_trace_eq_neg_leviCivita4 (a b c d : Fin 4) :
    Matrix.trace (diracOmega4 * spinBiv a b * PeirceSpine.comm (solderVec c) (solderVec d)) =
      -(InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d : ℝ) := by
  change Matrix.trace (diracOmega4 * spinBiv a b * spinBiv c d) = _
  rw [diracOmega4_eq_cast4, spinBiv_eq_quarter_cast4 a b, spinBiv_eq_quarter_cast4 c d]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [Matrix.trace_smul, ← cast4_mul, ← cast4_mul, cast4_trace, palatini_trace_Z a b c d,
    smul_eq_mul]
  exact palatini_scalar_sixteenth _

/-- Arbitrary real 2-form curvature bivector `R = ∑_{a,b} R^{ab} Σ_{ab}` in `M₄(ℝ)`. -/
def curvatureBivOp (R : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, R a b • spinBiv a b

/-- Soldering tetrad 1-form `e = ∑_a e^a e_a` in `M₄(ℝ)`. -/
def tetradVecOp (e : Fin 4 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  ∑ a : Fin 4, e a • solderVec a

/-- Area bivector `[e₁, e₂] = ∑_{c,d} e₁^c e₂^d Σ_{cd}` in `M₄(ℝ)`. -/
def areaBivOp (e₁ e₂ : Fin 4 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  PeirceSpine.comm (tetradVecOp e₁) (tetradVecOp e₂)

private lemma areaBivOp_expand (e₁ e₂ : Fin 4 → ℝ) :
    areaBivOp e₁ e₂ = ∑ c : Fin 4, ∑ d : Fin 4, (e₁ c * e₂ d) • spinBiv c d := by
  unfold areaBivOp tetradVecOp PeirceSpine.comm spinBiv
  have h1 : (∑ c : Fin 4, e₁ c • solderVec c) * (∑ d : Fin 4, e₂ d • solderVec d) =
      ∑ c : Fin 4, ∑ d : Fin 4, (e₁ c * e₂ d) • (solderVec c * solderVec d) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h2 : (∑ d : Fin 4, e₂ d • solderVec d) * (∑ c : Fin 4, e₁ c • solderVec c) =
      ∑ c : Fin 4, ∑ d : Fin 4, (e₁ c * e₂ d) • (solderVec d * solderVec c) := by
    have h2a : (∑ d : Fin 4, e₂ d • solderVec d) * (∑ c : Fin 4, e₁ c • solderVec c) =
        ∑ d : Fin 4, ∑ c : Fin 4, (e₁ c * e₂ d) • (solderVec d * solderVec c) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (e₂ d) (e₁ c)]
    rw [h2a, Finset.sum_comm]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← smul_sub]
  rfl

private lemma diracOmega4_comm_spinBiv (a b : Fin 4) :
    diracOmega4 * spinBiv a b = spinBiv a b * diracOmega4 :=
  (soldering_commutators_generate_spin_and_palatini_gravity a b 0).2.1

private lemma diracOmega4_anticomm_tetradVecOp (t : Fin 4 → ℝ) :
    diracOmega4 * tetradVecOp t = -(tetradVecOp t * diracOmega4) := by
  unfold tetradVecOp
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hAnti := eq_neg_of_add_eq_zero_left
    (soldering_commutators_generate_spin_and_palatini_gravity a 0 0).1
  rw [Matrix.mul_smul, Matrix.smul_mul, hAnti, smul_neg]

private lemma diracOmega4_comm_curvatureBivOp (R : Fin 4 → Fin 4 → ℝ) :
    diracOmega4 * curvatureBivOp R = curvatureBivOp R * diracOmega4 := by
  unfold curvatureBivOp
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, diracOmega4_comm_spinBiv a b]

private lemma diracOmega4_comm_areaBivOp (e₁ e₂ : Fin 4 → ℝ) :
    diracOmega4 * areaBivOp e₁ e₂ = areaBivOp e₁ e₂ * diracOmega4 := by
  rw [areaBivOp_expand, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, diracOmega4_comm_spinBiv c d]

private lemma palatini_biv_sum_trace (C₁ C₂ : Fin 4 → Fin 4 → ℝ) :
    Matrix.trace
      (diracOmega4 * (∑ a : Fin 4, ∑ b : Fin 4, C₁ a b • spinBiv a b) *
        (∑ c : Fin 4, ∑ d : Fin 4, C₂ c d • spinBiv c d)) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        C₁ a b * C₂ c d * (InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d : ℝ) := by
  have hL : diracOmega4 * (∑ a : Fin 4, ∑ b : Fin 4, C₁ a b • spinBiv a b) =
      ∑ a : Fin 4, ∑ b : Fin 4, C₁ a b • (diracOmega4 * spinBiv a b) := by
    simp only [Finset.mul_sum, Matrix.mul_smul]
  rw [hL, Finset.sum_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun d _ => ?_
  have hP : Matrix.trace (diracOmega4 * spinBiv a b * spinBiv c d) =
      -(InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d : ℝ) := by
    simpa [spinBiv] using palatini_trace_eq_neg_leviCivita4 a b c d
  rw [hP]
  ring

private lemma macdowell_mansouri_symm_trace_aux
    (Γ R E T : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (hSq : Γ * Γ = -1)
    (hGR : Γ * R = R * Γ) (hGE : Γ * E = E * Γ) (hGT : Γ * T = -(T * Γ)) :
    Matrix.trace (Γ * ((R + E) + T) * ((R + E) + T)) =
      Matrix.trace (Γ * R * R) + 2 * Matrix.trace (Γ * R * E) +
        Matrix.trace (Γ * E * E) + Matrix.trace (Γ * T * T) := by
  have hRE : Matrix.trace (Γ * E * R) = Matrix.trace (Γ * R * E) := by
    calc
      Matrix.trace (Γ * E * R) = Matrix.trace ((Γ * E) * R) := rfl
      _ = Matrix.trace (R * (Γ * E)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((R * Γ) * E) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Γ * R) * E) := by rw [← hGR]
      _ = Matrix.trace (Γ * R * E) := rfl
  have hRT : Matrix.trace (Γ * R * T) = 0 := by
    apply graded_odd_trace_zero Γ _ hSq
    calc
      Γ * (Γ * R * T) = (Γ * Γ) * (R * T) := by simp only [Matrix.mul_assoc]
      _ = Γ * ((Γ * R) * T) := by simp only [Matrix.mul_assoc]
      _ = Γ * (R * (Γ * T)) := by rw [hGR]; simp only [Matrix.mul_assoc]
      _ = -(Γ * R * T * Γ) := by rw [hGT]; noncomm_ring
  have hET : Matrix.trace (Γ * E * T) = 0 := by
    apply graded_odd_trace_zero Γ _ hSq
    calc
      Γ * (Γ * E * T) = Γ * ((Γ * E) * T) := by simp only [Matrix.mul_assoc]
      _ = Γ * (E * (Γ * T)) := by rw [hGE]; simp only [Matrix.mul_assoc]
      _ = -(Γ * E * T * Γ) := by rw [hGT]; noncomm_ring
  have hTR : Matrix.trace (Γ * T * R) = 0 := by
    calc
      Matrix.trace (Γ * T * R) = Matrix.trace ((Γ * T) * R) := rfl
      _ = Matrix.trace (R * (Γ * T)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((R * Γ) * T) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Γ * R) * T) := by rw [← hGR]
      _ = Matrix.trace (Γ * R * T) := rfl
      _ = 0 := hRT
  have hTE : Matrix.trace (Γ * T * E) = 0 := by
    calc
      Matrix.trace (Γ * T * E) = Matrix.trace ((Γ * T) * E) := rfl
      _ = Matrix.trace (E * (Γ * T)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((E * Γ) * T) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((Γ * E) * T) := by rw [← hGE]
      _ = Matrix.trace (Γ * E * T) := rfl
      _ = 0 := hET
  have hExp : Γ * ((R + E) + T) * ((R + E) + T) =
      (Γ * R * R + Γ * R * E + Γ * E * R + Γ * E * E) +
        (Γ * R * T + Γ * E * T + Γ * T * R + Γ * T * E + Γ * T * T) := by
    noncomm_ring
  rw [hExp, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    hRE, hRT, hET, hTR, hTE]
  ring

/-- **Theorem 4 (MacDowell–Mansouri Action Expansion into Gauss–Bonnet, Palatini, & Volume Terms)**:
On arbitrary curvature 2-form coefficients `R, R₁, R₂` and tetrad/torsion vectors `e₁, e₂, e₃, e₄, t`:
1. Topological Gauss–Bonnet term: `Tr(ω₄ R₁ R₂) = -∑ R₁^{ab} R₂^{cd} ε_{abcd}`.
2. Einstein–Hilbert–Palatini term: `Tr(ω₄ R [e₁, e₂]) = -∑ R^{ab} e₁^c e₂^d ε_{abcd}`.
3. Cosmological volume term: `Tr(ω₄ [e₁, e₂] [e₃, e₄]) = -∑ e₁^a e₂^b e₃^c e₄^d ε_{abcd}`.
4. Even–odd torsion cross-terms vanish identically: `Tr(ω₄ (R + [e₁, e₂]) t) = 0`.
5. Complete quadratic MacDowell–Mansouri expansion `Tr(ω₄ ((R + [e₁, e₂]) + t)²)` splits into
   Gauss–Bonnet + `2` Einstein–Hilbert–Palatini + Cosmological volume + torsion `Tr(ω₄ t²)`. -/
theorem macdowell_mansouri_action_expansion
    (R R₁ R₂ : Fin 4 → Fin 4 → ℝ) (e₁ e₂ e₃ e₄ t : Fin 4 → ℝ) :
    let E₁₂ := areaBivOp e₁ e₂
    let E₃₄ := areaBivOp e₃ e₄
    let Rop := curvatureBivOp R
    let R₁op := curvatureBivOp R₁
    let R₂op := curvatureBivOp R₂
    let Top := tetradVecOp t
    let ε := InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4
    (Matrix.trace (diracOmega4 * R₁op * R₂op) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R₁ a b * R₂ c d * (ε a b c d : ℝ)) ∧
    (Matrix.trace (diracOmega4 * Rop * E₁₂) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R a b * e₁ c * e₂ d * (ε a b c d : ℝ)) ∧
    (Matrix.trace (diracOmega4 * E₁₂ * E₃₄) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        e₁ a * e₂ b * e₃ c * e₄ d * (ε a b c d : ℝ)) ∧
    (Matrix.trace (diracOmega4 * (Rop + E₁₂) * Top) = 0) ∧
    (Matrix.trace (diracOmega4 * ((Rop + E₁₂) + Top) * ((Rop + E₁₂) + Top)) =
      (-∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R a b * R c d * (ε a b c d : ℝ)) +
      2 * (-∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R a b * e₁ c * e₂ d * (ε a b c d : ℝ)) +
      (-∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        e₁ a * e₂ b * e₁ c * e₂ d * (ε a b c d : ℝ)) +
      Matrix.trace (diracOmega4 * Top * Top)) := by
  dsimp only
  have hGB : Matrix.trace (diracOmega4 * curvatureBivOp R₁ * curvatureBivOp R₂) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R₁ a b * R₂ c d * (InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d : ℝ) := by
    unfold curvatureBivOp
    exact palatini_biv_sum_trace R₁ R₂
  have hEHP : Matrix.trace (diracOmega4 * curvatureBivOp R * areaBivOp e₁ e₂) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R a b * e₁ c * e₂ d * (InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d : ℝ) := by
    unfold curvatureBivOp
    rw [areaBivOp_expand]
    simpa [mul_assoc] using palatini_biv_sum_trace R (fun c d => e₁ c * e₂ d)
  have hVol : Matrix.trace (diracOmega4 * areaBivOp e₁ e₂ * areaBivOp e₃ e₄) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        e₁ a * e₂ b * e₃ c * e₄ d *
          (InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d : ℝ) := by
    rw [areaBivOp_expand e₁ e₂, areaBivOp_expand e₃ e₄]
    simpa [mul_assoc] using
      palatini_biv_sum_trace (fun a b => e₁ a * e₂ b) (fun c d => e₃ c * e₄ d)
  have hOdd : Matrix.trace (diracOmega4 * (curvatureBivOp R + areaBivOp e₁ e₂) * tetradVecOp t) = 0 := by
    apply graded_odd_trace_zero diracOmega4 _
      lorentz_spin_algebra_and_two_casimirs.2.2.2.2.2.1
    have hGEven : diracOmega4 * (curvatureBivOp R + areaBivOp e₁ e₂) =
        (curvatureBivOp R + areaBivOp e₁ e₂) * diracOmega4 := by
      rw [mul_add, add_mul, diracOmega4_comm_curvatureBivOp, diracOmega4_comm_areaBivOp]
    have hGT : diracOmega4 * tetradVecOp t = -(tetradVecOp t * diracOmega4) :=
      diracOmega4_anticomm_tetradVecOp t
    calc
      diracOmega4 * (diracOmega4 * (curvatureBivOp R + areaBivOp e₁ e₂) * tetradVecOp t)
          = diracOmega4 * ((diracOmega4 * (curvatureBivOp R + areaBivOp e₁ e₂)) * tetradVecOp t) := by
            simp only [Matrix.mul_assoc]
      _ = diracOmega4 * ((curvatureBivOp R + areaBivOp e₁ e₂) * (diracOmega4 * tetradVecOp t)) := by
            rw [hGEven]; simp only [Matrix.mul_assoc]
      _ = -(diracOmega4 * (curvatureBivOp R + areaBivOp e₁ e₂) * tetradVecOp t * diracOmega4) := by
            rw [hGT]; noncomm_ring
  refine ⟨hGB, hEHP, hVol, hOdd, ?_⟩
  rw [macdowell_mansouri_symm_trace_aux diracOmega4 (curvatureBivOp R) (areaBivOp e₁ e₂) (tetradVecOp t)
    lorentz_spin_algebra_and_two_casimirs.2.2.2.2.2.1
    (diracOmega4_comm_curvatureBivOp R) (diracOmega4_comm_areaBivOp e₁ e₂)
    (diracOmega4_anticomm_tetradVecOp t)]
  have hGB_self : Matrix.trace (diracOmega4 * curvatureBivOp R * curvatureBivOp R) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        R a b * R c d * (InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d : ℝ) := by
    unfold curvatureBivOp
    exact palatini_biv_sum_trace R R
  have hVol_self : Matrix.trace (diracOmega4 * areaBivOp e₁ e₂ * areaBivOp e₁ e₂) =
      -∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        e₁ a * e₂ b * e₁ c * e₂ d *
          (InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 a b c d : ℝ) := by
    rw [areaBivOp_expand e₁ e₂]
    simpa [mul_assoc] using
      palatini_biv_sum_trace (fun a b => e₁ a * e₂ b) (fun c d => e₁ c * e₂ d)
  rw [hGB_self, hEHP, hVol_self]

end InfoGeometry.Canonical.RoadToGravityFromSpinning