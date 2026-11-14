/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.NoncommutativeFutureHorizonsTower

/-!
# Noncommutative All-Scales Inductive Tower & Historical Contrast Synthesis

This module synthesizes the all-scales inductive tower $\mathcal{C}\ell_n(A)$ (`IT₁`–`IT₃`)
together with the five historical contrast theorems (`IT₄` : `CM₁`–`CM₅`) over arbitrary
noncommutative rings `[Ring B]` and $\star$-rings `[Ring A] [StarRing A]`.

## Archetypes (`IT₁`–`IT₄`)
* `IT₁` (`all_scales_inductive_witt_cantor_chiral_hodge`): All-scales square-zero chiral Hodge
  axioms for `(wittTowerD n, wittTowerDelta n)` on `ClTower (n + 1) A`, with exact Hodge
  projection `d_n * δ_n = cantorTowerProj (n + 1)` and harmonic kernel equivalence.
* `IT₂` (`all_scales_inductive_supertrace_and_jump_cancellation`): All-scales chirality grading
  `gammaTowerOp n`, invariant supertrace `towerSuperTrace n (cantorTowerProj n) = 1`, and
  jumping-mode cancellation `towerSuperTrace (n + 1) (mat2 δ 0 0 δ) = 0`.
* `IT₃` (`all_scales_dyadic_rg_trajectory_invariance`): `2 ^ k * N`-horizon dyadic RG trajectory
  decimation invariance `trajectoryMean N (rgBlockIter k traj) = trajectoryMean (2 ^ k * N) traj`.
* `IT₄` (`master_historical_contrast_synthesis`): Unified contrast theorems `CM₁`–`CM₅`
  contrasting central/commuting/orthogonal reductions against noncommutative parabolic monodromy,
  Cayley–Peirce FUP variance, quaternion braid curvature, `sl₂` Lie cross-product obstruction,
  and non-orthogonal unipotent infinite order.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeFutureHorizonsTower

namespace InfoGeometry.Algebra.NoncommutativeAllScalesTowerAndContrastSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of fun i j => match i, j with
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

@[simp] lemma mat2_00 {A : Type*} (a b c d : A) : (mat2 a b c d) 0 0 = a := rfl
@[simp] lemma mat2_01 {A : Type*} (a b c d : A) : (mat2 a b c d) 0 1 = b := rfl
@[simp] lemma mat2_10 {A : Type*} (a b c d : A) : (mat2 a b c d) 1 0 = c := rfl
@[simp] lemma mat2_11 {A : Type*} (a b c d : A) : (mat2 a b c d) 1 1 = d := rfl

@[simp] lemma tr2_00 {A : Type*} (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 0 = M 0 0 := rfl
@[simp] lemma tr2_01 {A : Type*} (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 0 1 = M 1 0 := rfl
@[simp] lemma tr2_10 {A : Type*} (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 0 = M 0 1 := rfl
@[simp] lemma tr2_11 {A : Type*} (M : Matrix (Fin 2) (Fin 2) A) : Mᵀ 1 1 = M 1 1 := rfl

@[simp] lemma ct2_00 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 0 = star (M 0 0) := rfl
@[simp] lemma ct2_01 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 0 1 = star (M 1 0) := rfl
@[simp] lemma ct2_10 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 0 = star (M 0 1) := rfl
@[simp] lemma ct2_11 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : Mᴴ 1 1 = star (M 1 1) := rfl

variable {A : Type*} [Ring A]

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

/-!
## Stratum $\mathcal{I}\mathcal{T}_1$ & $\mathcal{I}\mathcal{T}_2$: All-Scales Witt–Cantor Chiral Hodge & Atiyah–Singer Supertrace on $\mathcal{C}\ell_n(A)$
-/

section StratumIT1_IT2_InductiveHodgeAndSupertrace

universe u

variable {A : Type u} [Ring A]

/-- The $n$-scale chirality grading involution $\Gamma^{(n)} \in \mathcal{C}\ell_n(A)$. -/
def gammaTowerOp : ∀ n : ℕ, ClTower n A
  | 0     => (1 : A)
  | n + 1 => mat2 (gammaTowerOp n) 0 0 (-gammaTowerOp n)

/-- Iterated $n$-scale Atiyah–Singer supertrace $\mathrm{Str}_{2^n}(M) = \mathrm{Tr}_{2^n}(\Gamma^{(n)} M)$. -/
def towerSuperTrace (n : ℕ) (M : ClTower n A) : A :=
  towerTrace n (gammaTowerOp n * M)

/-- The $(n+1)$-scale coupled isotropic Witt differentials $d_n, \delta_n \in \mathcal{C}\ell_{n+1}(A)$. -/
def wittTowerD (n : ℕ) : ClTower (n + 1) A :=
  mat2 0 (cantorTowerProj n) 0 0

def wittTowerDelta (n : ℕ) : ClTower (n + 1) A :=
  mat2 0 0 (cantorTowerProj n) 0

/-- **All-Scales Inductive Witt–Cantor Chiral Hodge Theorem ($\mathcal{I}\mathcal{T}_1$)**:
At every scale $n \in \mathbb{N}$ in $\mathcal{C}\ell_{n+1}(A)$:
1. $d_n^2 = 0$, $\delta_n^2 = 0$, $d_n \delta_n d_n = d_n$, $\delta_n d_n \delta_n = \delta_n$,
2. The exact Hodge projection $d_n \delta_n$ is identically $\Pi_{\mathcal{C}_{n+1}}$,
3. For any $\mathbb{X} \in \mathcal{C}\ell_{n+1}(A)$,
   $(d_n + \delta_n)\mathbb{X} = 0 \iff (1 - (d_n\delta_n + \delta_n d_n))\mathbb{X} = \mathbb{X}$. -/
theorem all_scales_inductive_witt_cantor_chiral_hodge (n : ℕ) (X : ClTower (n + 1) A) :
    let d_n   := (wittTowerD n : ClTower (n + 1) A)
    let del_n := (wittTowerDelta n : ClTower (n + 1) A)
    d_n * d_n = 0 ∧
    del_n * del_n = 0 ∧
    d_n * del_n * d_n = d_n ∧
    del_n * d_n * del_n = del_n ∧
    d_n * del_n = cantorTowerProj (n + 1) ∧
    ((d_n + del_n) * X = 0 ↔ (1 - (d_n * del_n + del_n * d_n)) * X = X) := by
  have h_idem := cantorTowerProj_idem (A := A) n
  have hd2 : (wittTowerD n : ClTower (n + 1) A) * wittTowerD n = 0 := by
    apply ext_fin2 <;> simp [wittTowerD]
  have hdel2 : (wittTowerDelta n : ClTower (n + 1) A) * wittTowerDelta n = 0 := by
    apply ext_fin2 <;> simp [wittTowerDelta]
  have hddeld : (wittTowerD n : ClTower (n + 1) A) * wittTowerDelta n * wittTowerD n = wittTowerD n := by
    apply ext_fin2 <;> simp [wittTowerD, wittTowerDelta, h_idem]
  have hdelddel : (wittTowerDelta n : ClTower (n + 1) A) * wittTowerD n * wittTowerDelta n = wittTowerDelta n := by
    apply ext_fin2 <;> simp [wittTowerD, wittTowerDelta, h_idem]
  have h_ex : (wittTowerD n : ClTower (n + 1) A) * wittTowerDelta n = cantorTowerProj (n + 1) := by
    apply ext_fin2 <;> simp [wittTowerD, wittTowerDelta, cantorTowerProj, h_idem]
  refine ⟨hd2, hdel2, hddeld, hdelddel, h_ex, ?_⟩
  constructor
  · intro h
    have h1 : wittTowerD n * X = 0 := by
      calc wittTowerD n * X
        _ = (wittTowerD n * wittTowerDelta n * wittTowerD n) * X +
            wittTowerD n * (wittTowerDelta n * wittTowerDelta n) * X := by
            rw [hddeld, hdel2]; noncomm_ring
        _ = wittTowerD n * wittTowerDelta n * ((wittTowerD n + wittTowerDelta n) * X) := by
            noncomm_ring
        _ = wittTowerD n * wittTowerDelta n * 0 := by rw [h]
        _ = 0 := mul_zero _
    have h2 : wittTowerDelta n * X = 0 := by
      calc wittTowerDelta n * X
        _ = wittTowerDelta n * (wittTowerD n * wittTowerD n) * X +
            (wittTowerDelta n * wittTowerD n * wittTowerDelta n) * X := by
            rw [hd2, hdelddel]; noncomm_ring
        _ = wittTowerDelta n * wittTowerD n * ((wittTowerD n + wittTowerDelta n) * X) := by
            noncomm_ring
        _ = wittTowerDelta n * wittTowerD n * 0 := by rw [h]
        _ = 0 := mul_zero _
    calc (1 - (wittTowerD n * wittTowerDelta n + wittTowerDelta n * wittTowerD n)) * X
      _ = X - wittTowerD n * (wittTowerDelta n * X) -
          wittTowerDelta n * (wittTowerD n * X) := by noncomm_ring
      _ = X - wittTowerD n * 0 - wittTowerDelta n * 0 := by rw [h1, h2]
      _ = X := by noncomm_ring
  · intro hP
    calc (wittTowerD n + wittTowerDelta n) * X
      _ = (wittTowerD n + wittTowerDelta n) *
          ((1 - (wittTowerD n * wittTowerDelta n + wittTowerDelta n * wittTowerD n)) * X) := by
          rw [hP]
      _ = (wittTowerD n - wittTowerD n * wittTowerDelta n * wittTowerD n -
           (wittTowerD n * wittTowerD n) * wittTowerDelta n +
           wittTowerDelta n - (wittTowerDelta n * wittTowerDelta n) * wittTowerD n -
           wittTowerDelta n * wittTowerD n * wittTowerDelta n) * X := by noncomm_ring
      _ = (wittTowerD n - wittTowerD n - 0 * wittTowerDelta n +
           wittTowerDelta n - 0 * wittTowerD n - wittTowerDelta n) * X := by
          rw [hddeld, hd2, hdel2, hdelddel]
      _ = 0 := by noncomm_ring

/-- **All-Scales Inductive Atiyah–Singer Supertrace Theorem ($\mathcal{I}\mathcal{T}_2$)**:
For every scale $n \in \mathbb{N}$:
1. $(\Gamma^{(n)})^2 = 1$ and $\Gamma^{(n)} \Pi_{\mathcal{C}_n} = \Pi_{\mathcal{C}_n}$,
2. $\mathrm{Str}_{2^n}(\Pi_{\mathcal{C}_n}) = 1_A$,
3. For any spectral jump $\delta \in \mathcal{C}\ell_n(A)$, $\mathrm{Str}_{2^{n+1}}(\mathrm{diag}(\delta, \delta)) = 0$. -/
theorem all_scales_inductive_supertrace_and_jump_cancellation
    (n : ℕ) (δ : ClTower n A) :
    (gammaTowerOp n : ClTower n A) * gammaTowerOp n = 1 ∧
    (gammaTowerOp n : ClTower n A) * cantorTowerProj n = cantorTowerProj n ∧
    towerSuperTrace n (cantorTowerProj n : ClTower n A) = 1 ∧
    towerSuperTrace (n + 1) (mat2 δ 0 0 δ : ClTower (n + 1) A) = 0 := by
  have h_gamma_sq : ∀ k : ℕ, (gammaTowerOp k : ClTower k A) * gammaTowerOp k = 1 := by
    intro k; induction' k with k ih
    · exact mul_one 1
    · apply ext_fin2 <;> simp [gammaTowerOp, ih]
  have h_gamma_cantor : ∀ k : ℕ,
      (gammaTowerOp k : ClTower k A) * cantorTowerProj k = cantorTowerProj k := by
    intro k; induction' k with k ih
    · exact mul_one 1
    · apply ext_fin2 <;> simp [gammaTowerOp, cantorTowerProj, ih]
  have h_cantor_tr : ∀ k : ℕ, towerTrace k (cantorTowerProj k : ClTower k A) = 1 := by
    intro k; induction' k with k ih
    · rfl
    · dsimp [towerTrace, rgTowerDecimate, cantorTowerProj]
      rw [add_zero, ih]
  refine ⟨h_gamma_sq n, h_gamma_cantor n, ?_, ?_⟩
  · dsimp [towerSuperTrace]
    rw [h_gamma_cantor n, h_cantor_tr n]
  · dsimp [towerSuperTrace, towerTrace, rgTowerDecimate, gammaTowerOp]
    simp [towerTrace_zero n]

end StratumIT1_IT2_InductiveHodgeAndSupertrace

/-!
## Stratum $\mathcal{I}\mathcal{T}_3$: All-Scales $2^k N$-Horizon Dyadic RG Trajectory Decimation
-/

section StratumIT3_AllScalesDyadicRGTrajectory

variable {B : Type*} [Ring B]

def rgBlockStep (X : ℕ → B) (m : ℕ) : B :=
  X (2 * m) + X (2 * m + 1)

def rgBlockIter : ℕ → (ℕ → B) → (ℕ → B)
  | 0, traj     => traj
  | k + 1, traj => rgBlockStep (rgBlockIter k traj)

def trajectoryMean (N : ℕ) (X : ℕ → B) : B :=
  ∑ m ∈ Finset.range N, X m

theorem trajectoryMean_rgBlockStep (N : ℕ) (traj : ℕ → B) :
    trajectoryMean N (rgBlockStep traj) = trajectoryMean (2 * N) traj := by
  dsimp [trajectoryMean, rgBlockStep]
  induction' N with N ih
  · simp
  · have h2N : 2 * (N + 1) = 2 * N + 1 + 1 := by omega
    rw [Finset.sum_range_succ, ih, h2N, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]

/-- **All-Scales $2^k N$-Horizon Dyadic RG Trajectory Invariance ($\mathcal{I}\mathcal{T}_3$)**:
For every decimation depth $k \in \mathbb{N}$ and every horizon $N \in \mathbb{N}$,
$\mathrm{trajectoryMean}\; N\; (\mathrm{rgBlockIter}\; k\; \mathrm{traj}) = \mathrm{trajectoryMean}\; (2^k * N)\; \mathrm{traj}$. -/
theorem all_scales_dyadic_rg_trajectory_invariance (k N : ℕ) (traj : ℕ → B) :
    trajectoryMean N (rgBlockIter k traj) = trajectoryMean (2 ^ k * N) traj := by
  induction' k with k ih generalizing N
  · simp [rgBlockIter]
  · rw [rgBlockIter, trajectoryMean_rgBlockStep, ih (2 * N)]
    have h_pow : 2 ^ k * (2 * N) = 2 ^ (k + 1) * N := by
      rw [pow_succ, mul_assoc]
    rw [h_pow]

end StratumIT3_AllScalesDyadicRGTrajectory

/-!
## Stratum $\mathcal{I}\mathcal{T}_4$: The Five Decisive Historical Contrast Theorems ($\mathcal{C}\mathcal{M}_1$–$\mathcal{C}\mathcal{M}_5$)
-/

section StratumIT4_HistoricalContrastTheorems

abbrev NestedMat (B : Type*) := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B)

def conjBy {G : Type*} [Group G] (x q : G) : G := x * q * x⁻¹

def twistedCocycle {G : Type*} [Group G] (X Q : G) : ℕ → G
  | 0     => 1
  | n + 1 => Q * conjBy X (twistedCocycle X Q n)

theorem central_cocycle_collapses_to_pow {G : Type*} [Group G] {X Q : G}
    (h_comm : X * Q = Q * X) (n : ℕ) :
    twistedCocycle X Q n = Q ^ n := by
  have h_conj : ∀ k : ℕ, X * Q ^ k * X⁻¹ = Q ^ k := by
    intro k; induction' k with k ih
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

def symCompress {B : Type*} [Ring B] (P Q : B) : B := P * Q * P
def cayleyOp {A : Type*} [Ring A] : Matrix (Fin 2) (Fin 2) A := 1 + omegaOp
def mcCurvature {B : Type*} [Ring B] (d₁ d₂ : B →+ B) (A₁ A₂ : B) : B := d₁ A₂ - d₂ A₁ + ⁅A₁, A₂⁆
def flowGen {A : Type*} [Ring A] (cGamma cSigma cOmega : A) : Matrix (Fin 2) (Fin 2) A :=
  fiberEmbed cGamma * gamma1Op + fiberEmbed cSigma * sigmaOp + fiberEmbed cOmega * omegaOp

def E₁ {A : Type*} [Ring A] : NestedMat A := omegaOp
def E₂ {A : Type*} [Ring A] : NestedMat A := kleinTwist omegaOp
def E₃ {A : Type*} [Ring A] : NestedMat A := (E₁ : NestedMat A) * E₂

def T1_orth   : NestedMat ℤ := sigmaOp
def T2_orth   : NestedMat ℤ := mat2 omegaOp 0 0 1
def A_torsion : NestedMat ℤ := mat2 (-omegaOp) 0 0 omegaOp

/-- **Master Historical Contrast Theorem ($\mathcal{I}\mathcal{T}_4 \text{ : }\mathcal{C}\mathcal{M}_1$–$\mathcal{C}\mathcal{M}_5$)**:
Contrasts commutative/central/orthogonal reductions against our noncommutative operator constructions. -/
theorem master_historical_contrast_synthesis
    {A : Type*} [Ring A] [StarRing A] [CharZero A]
    {P Q : A} (hP : P * P = P) (hQ : Q * Q = Q) (hPQ_comm : ⁅P, Q⁆ = 0)
    {A₁ A₂ : A} (hA_comm : ⁅A₁, A₂⁆ = 0)
    (cGamma cSigma cOmega : A) (n : ℕ) (hn : 0 < n) :
    let Q_dual : Matrix (Fin 2) (Fin 2) A := cayleyOp * P_plus * cayleyOpᴴ
    let T_fup  : Matrix (Fin 2) (Fin 2) A := symCompress P_plus Q_dual
    -- CM₁: Parabolic block monodromy of infinite order despite order-2 generators & 1-cocycle closure
    ((X_blk : NestedMat A) * X_blk = 1 ∧
     (Z_blk : NestedMat A) * Z_blk = 1 ∧
     (Q_blk : NestedMat A) * (X_blk * Q_blk * X_blk) = 1 ∧
     (Q_blk : NestedMat A) ^ n = 1 + n • N_blk ∧
     (Q_blk : NestedMat A) ^ n ≠ 1) ∧
    -- CM₂: Commuting projection variance collapse vs. non-zero Cayley–Peirce FUP variance
    (symCompress P Q - symCompress P Q * symCompress P Q = 0 ∧
     ⁅(P_plus : Matrix (Fin 2) (Fin 2) A), Q_dual⁆ = -omegaOp ∧
     2 • T_fup - T_fup * T_fup = (P_plus : Matrix (Fin 2) (Fin 2) A)) ∧
    -- CM₃ & CM₄: Constant Abelian curvature collapse vs. quaternion curvature & Lie cross-product
    (mcCurvature (0 : A →+ A) 0 A₁ A₂ = 0 ∧
     mcCurvature (0 : NestedMat A →+ NestedMat A) 0 (E₁ : NestedMat A) E₂ = 2 • E₃ ∧
     flowGen cGamma cSigma cOmega * flowGen cGamma cSigma cOmega -
       fiberEmbed (cGamma * cGamma + cSigma * cSigma - cOmega * cOmega) * 1 =
       fiberEmbed ⁅cSigma, cOmega⁆ * gamma1Op +
       fiberEmbed ⁅cOmega, cGamma⁆ * sigmaOp -
       fiberEmbed ⁅cGamma, cSigma⁆ * omegaOp) ∧
    -- CM₅: Orthogonal gapped finite-order torsion vs. non-orthogonal unipotent infinite order
    ((T1_orth : NestedMat ℤ)ᴴ * T1_orth = 1 ∧
     (T2_orth : NestedMat ℤ)ᴴ * T2_orth = 1 ∧
     T1_orth * T2_orth = A_torsion * T2_orth * T1_orth ∧
     (A_torsion : NestedMat ℤ) ^ 2 ≠ 1 ∧
     (A_torsion : NestedMat ℤ) ^ 4 = 1 ∧
     (X_blk : NestedMat ℤ)ᴴ * X_blk ≠ 1) := by
  have hQ_decomp : (Q_blk : NestedMat A) = 1 + N_blk := by
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, sigmaOp, gamma1Op, F_plus, F_minus, N_blk, N_plus]
  have hN2 : (N_blk : NestedMat A) * N_blk = 0 := by
    apply ext_fin2 <;> apply ext_fin2 <;> simp [N_blk, N_plus, F_minus]
  have hPow : ∀ k : ℕ, (Q_blk : NestedMat A) ^ k = 1 + k • N_blk := by
    intro k; induction' k with k ih
    · simp
    · rw [pow_succ, ih, hQ_decomp, add_nsmul, one_nsmul]
      have h_mul : (k • (N_blk : NestedMat A)) * N_blk = 0 := by
        rw [nsmul_eq_mul, mul_assoc, hN2, mul_zero]
      calc (1 + k • (N_blk : NestedMat A)) * (1 + N_blk)
        _ = 1 + (k • N_blk + N_blk) + (k • N_blk) * N_blk := by noncomm_ring
        _ = 1 + (k • N_blk + N_blk) := by rw [h_mul, add_zero]
  have hPQ : P * Q = Q * P := sub_eq_zero.mp (by rw [← Ring.lie_def, hPQ_comm])
  refine ⟨⟨?_, ?_, ?_, hPow n, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
          ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [X_blk, F_plus]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [Z_blk, sigmaOp, gamma1Op]
  · apply ext_fin2 <;> apply ext_fin2 <;>
      simp [Q_blk, Z_blk, X_blk, sigmaOp, gamma1Op, F_plus]
  · intro h_eq
    have h_entry : (((Q_blk : NestedMat A) ^ n) 1 1) 1 0 = ((1 : NestedMat A) 1 1) 1 0 := by
      rw [h_eq]
    rw [hPow n] at h_entry
    have h_zero : (n : A) = 0 := by
      simp [N_blk, F_minus] at h_entry
      exact h_entry
    exact Nat.ne_of_gt hn (Nat.cast_eq_zero.mp h_zero)
  · dsimp [symCompress]
    have h_idem : P * Q * P * (P * Q * P) = P * Q * P := by
      calc P * Q * P * (P * Q * P)
          = P * Q * (P * P) * Q * P := by noncomm_ring
        _ = P * Q * (P * Q) * P := by rw [hP]; noncomm_ring
        _ = P * Q * (Q * P) * P := by nth_rw 2 [hPQ]
        _ = P * (Q * Q) * (P * P) := by noncomm_ring
        _ = P * Q * P := by rw [hQ, hP]
    rw [h_idem, sub_self]
  · rw [Ring.lie_def]
    apply ext_fin2 <;> simp [cayleyOp, P_plus, omegaOp]
  · apply ext_fin2 <;> simp [symCompress, cayleyOp, P_plus, omegaOp, two_smul]
  · dsimp [mcCurvature]; simp [hA_comm]
  · dsimp [mcCurvature]; rw [Ring.lie_def]
    apply ext_fin2 <;> apply ext_fin2 <;>
      simp [E₁, E₂, E₃, kleinTwist, omegaOp, two_smul]
  · simp only [Ring.lie_def]
    apply ext_fin2 <;> simp [flowGen, fiberEmbed, gamma1Op, sigmaOp, omegaOp] <;> noncomm_ring
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [T1_orth, sigmaOp]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [T2_orth, omegaOp]
  · apply ext_fin2 <;> apply ext_fin2 <;> simp [T1_orth, T2_orth, A_torsion, sigmaOp, omegaOp]
  · intro h
    have h00 : (((A_torsion : NestedMat ℤ) ^ 2) 0 0) 0 0 = ((1 : NestedMat ℤ) 0 0) 0 0 := by
      rw [h]
    simp [A_torsion, omegaOp, sq] at h00
  · rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
    apply ext_fin2 <;> apply ext_fin2 <;> simp [A_torsion, omegaOp, sq]
  · exact (by decide : (X_blk : NestedMat ℤ)ᴴ * X_blk ≠ 1)

end StratumIT4_HistoricalContrastTheorems


private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

end InfoGeometry.Algebra.NoncommutativeAllScalesTowerAndContrastSynthesis
