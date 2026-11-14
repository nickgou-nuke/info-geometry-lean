/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.NoncommutativeFutureHorizonsTower

/-!
# Noncommutative Tower Transition Laws & All-Scales Spectral Mass Gap Synthesis

This module formalizes the directed inductive system $(\mathcal{C}\ell_n(A), \iota_{\mathrm{Cantor}}^{(n)})$,
the transition-compatible trace cocone laws for both `towerTrace` and
`superTrace` (`MG₁`–`MG₂`), the all-scales Hodge–Witten Laplacian spectral gap (`MG₃`), and
the all-scales spectral mass gap Hamiltonian with the $(2^n - 1)$ excited pore FUP energy law (`MG₄`),
over arbitrary noncommutative rings `[Ring A]` and $\star$-rings `[Ring A] [StarRing A]`.

The Cantor corner transition is multiplicative but non-unital, so these results
establish compatible finite-stage traces, not a colimit in `RingCat` or its
universal property. The unital diagonal amplification is a different transition.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeFutureHorizonsTower

namespace InfoGeometry.Algebra.NoncommutativeColimitAndSpectralGapSynthesis

universe u

variable {A : Type u} [Ring A]

def gammaTowerOp : ∀ n : ℕ, ClTower n A
  | 0     => (1 : A)
  | n + 1 => mat2 (gammaTowerOp n) 0 0 (-gammaTowerOp n)

lemma towerTrace_add : ∀ {n : ℕ} (X Y : ClTower n A),
    towerTrace n (X + Y) = towerTrace n X + towerTrace n Y
  | 0,     _, _ => rfl
  | _ + 1, X, Y => by
      dsimp [towerTrace, rgTowerDecimate]
      have h_comm : (X 0 0 + Y 0 0) + (X 1 1 + Y 1 1) = (X 0 0 + X 1 1) + (Y 0 0 + Y 1 1) := by
        abel
      rw [h_comm, towerTrace_add]

lemma towerTrace_nsmul (n : ℕ) (j : ℕ) (X : ClTower n A) :
    towerTrace n (j • X) = j • towerTrace n X := by
  induction j with
  | zero => simp [towerTrace_zero]
  | succ j ih =>
      rw [succ_nsmul, towerTrace_add, ih, succ_nsmul]

lemma gammaTowerOp_cantorTowerProj : ∀ n : ℕ,
    (gammaTowerOp n : ClTower n A) * cantorTowerProj n = cantorTowerProj n
  | 0 => mul_one 1
  | n + 1 => by
      apply ext_fin2 <;> simp [gammaTowerOp, cantorTowerProj, gammaTowerOp_cantorTowerProj n]

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower n A), towerTrace n (-X) = -towerTrace n X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace, rgTowerDecimate]
      have h_neg : -X 0 0 + -X 1 1 = -(X 0 0 + X 1 1) := by abel
      rw [h_neg, towerTrace_neg]

def superTrace {n : ℕ} (M : ClTower n A) : A :=
  towerTrace n (gammaTowerOp n * M)

/-!
## Archetype $\mathcal{M}\mathcal{G}_1$ & $\mathcal{M}\mathcal{G}_2$: Directed Inductive System & Trace-Compatible Cocone Laws
-/

section ArchetypeMG1_MG2_InductiveColimitCocone

/-- Infrared / vacuum corner transition homomorphism $\iota_{\mathrm{Cantor}}^{(n)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+1}(A)$. -/
def cantorEmbed (n : ℕ) (X : ClTower n A) : ClTower (n + 1) A :=
  mat2 X 0 0 0

/-- Bulk diagonal transition homomorphism $\iota_{\mathrm{diag}}^{(n)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+1}(A)$. -/
def diagEmbed (n : ℕ) (X : ClTower n A) : ClTower (n + 1) A :=
  mat2 X 0 0 X

/-- Multi-step directed transition functor $\iota_{\mathrm{Cantor}}^{(n, n+k)} : \mathcal{C}\ell_n(A) \to \mathcal{C}\ell_{n+k}(A)$. -/
def cantorEmbedIter (n : ℕ) : ∀ (k : ℕ), ClTower n A → ClTower (n + k) A
  | 0,     X => X
  | k + 1, X => cantorEmbed (n + k) (cantorEmbedIter n k X)

theorem towerTrace_cantorEmbed (n : ℕ) (X : ClTower n A) :
    towerTrace (n + 1) (cantorEmbed n X) = towerTrace n X := by
  dsimp [towerTrace, rgTowerDecimate, cantorEmbed]
  simp

theorem cantorEmbed_add (n : ℕ) (X Y : ClTower n A) :
    cantorEmbed n (X + Y) = cantorEmbed n X + cantorEmbed n Y := by
  apply ext_fin2 <;> simp [cantorEmbed]

theorem cantorEmbed_mul (n : ℕ) (X Y : ClTower n A) :
    cantorEmbed n (X * Y) = cantorEmbed n X * cantorEmbed n Y := by
  apply ext_fin2 <;> simp [cantorEmbed]

theorem cantorEmbed_zero (n : ℕ) :
    cantorEmbed n (0 : ClTower n A) = 0 := by
  apply ext_fin2 <;> simp [cantorEmbed]

theorem cantorEmbed_star [StarRing A] (n : ℕ) (X : ClTower n A) :
    cantorEmbed n (star X) = star (cantorEmbed n X) := by
  apply ext_fin2 <;> simp [cantorEmbed, mat2]

theorem superTrace_cantorEmbed (n : ℕ) (X : ClTower n A) :
    superTrace (cantorEmbed n X) = superTrace X := by
  dsimp [superTrace, cantorEmbed, gammaTowerOp, towerTrace, rgTowerDecimate]
  simp

theorem towerTrace_diagEmbed (n : ℕ) (X : ClTower n A) :
    towerTrace (n + 1) (diagEmbed n X) = 2 • towerTrace n X := by
  dsimp [towerTrace, rgTowerDecimate, diagEmbed]
  rw [towerTrace_add, two_smul]

/-- **Inter-Scale Transition and Trace Compatibility Theorem ($\mathcal{M}\mathcal{G}_1$ & $\mathcal{M}\mathcal{G}_2$)**:
1. $\iota_{\mathrm{Cantor}}^{(n)}$ is a multiplicative homomorphism mapping $\Pi_{\mathcal{C}_n} \mapsto \Pi_{\mathcal{C}_{n+1}}$,
2. RG block decimation $\mathcal{R}_{\mathrm{RG}}^{(n)}$ is an exact retraction: $\mathcal{R}_{\mathrm{RG}}^{(n)}(\iota_{\mathrm{Cantor}}^{(n)}(X)) = X$,
3. The bulk diagonal embedding $\iota_{\mathrm{diag}}^{(n)}$ is annihilated by $\mathrm{Str}_{2^{n+1}}$,
4. Multi-step directed transitions $\iota_{\mathrm{Cantor}}^{(n, n+k)}$ strictly preserve both
   $\mathrm{Tr}_{2^n}$ and $\mathrm{Str}_{2^n}$ across all $n, k \in \mathbb{N}$. -/
theorem cantor_transition_trace_and_supertrace_compatibility
    (n k : ℕ) (X Y : ClTower n A) :
    cantorEmbed n (X * Y) = cantorEmbed n X * cantorEmbed n Y ∧
    cantorEmbed n (cantorTowerProj (A := A) n) = cantorTowerProj (n + 1) ∧
    rgTowerDecimate n (cantorEmbed n X) = X ∧
    towerTrace (n + 1) (diagEmbed n X) = 2 • towerTrace n X ∧
    superTrace (diagEmbed n X) = 0 ∧
    towerTrace (n + k) (cantorEmbedIter n k X) = towerTrace n X ∧
    superTrace (cantorEmbedIter n k X) = superTrace X := by
  refine ⟨?_, rfl, ?_, towerTrace_diagEmbed n X, ?_, ?_, ?_⟩
  · apply ext_fin2 <;> simp [cantorEmbed]
  · dsimp [rgTowerDecimate, cantorEmbed]; simp
  · dsimp [superTrace, diagEmbed, gammaTowerOp, towerTrace, rgTowerDecimate]
    simp [neg_mul, towerTrace_zero]
  · induction' k with m ih
    · rfl
    · dsimp [cantorEmbedIter]
      change towerTrace (n + m + 1) (cantorEmbed (n + m) (cantorEmbedIter n m X)) = towerTrace n X
      rw [towerTrace_cantorEmbed (n + m), ih]
  · induction' k with m ih
    · rfl
    · dsimp [cantorEmbedIter]
      change superTrace (cantorEmbed (n + m) (cantorEmbedIter n m X)) = superTrace X
      rw [superTrace_cantorEmbed (n + m), ih]

end ArchetypeMG1_MG2_InductiveColimitCocone

/-!
## Archetype $\mathcal{M}\mathcal{G}_3$: All-Scales Hodge–Witten Laplacian $\Delta_{n+1} = (d_n + \delta_n)^2$
-/

section ArchetypeMG3_AllScalesHodgeLaplacian

def wittD (n : ℕ) : ClTower (n + 1) A := mat2 0 (cantorTowerProj n) 0 0
def wittDelta (n : ℕ) : ClTower (n + 1) A := mat2 0 0 (cantorTowerProj n) 0

/-- The $(n+1)$-scale Hodge–Witten Laplacian $\Delta_{n+1} = (d_n + \delta_n)^2 \in \mathcal{C}\ell_{n+1}(A)$. -/
def hodgeLaplacian (n : ℕ) : ClTower (n + 1) A :=
  (wittD n + wittDelta n) * (wittD n + wittDelta n)

/-- **All-Scales Hodge–Witten Laplacian Spectral Gap Theorem ($\mathcal{M}\mathcal{G}_3$)**:
At every scale $n \in \mathbb{N}$:
1. $\Delta_{n+1} = d_n \delta_n + \delta_n d_n = \mathrm{diag}(\Pi_{\mathcal{C}_n}, \Pi_{\mathcal{C}_n})$,
2. $\Delta_{n+1}^2 = \Delta_{n+1}$ (an algebraic idempotent decomposition),
3. $\Delta_{n+1} \Pi_{\mathcal{C}_{n+1}} = \Pi_{\mathcal{C}_{n+1}}$ and $\Delta_{n+1}(1 - \Delta_{n+1}) = 0$. -/
theorem all_scales_hodge_laplacian_spectral_gap (n : ℕ) :
    hodgeLaplacian (A := A) n = wittD n * wittDelta n + wittDelta n * wittD n ∧
    hodgeLaplacian (A := A) n = mat2 (cantorTowerProj n) 0 0 (cantorTowerProj n) ∧
    hodgeLaplacian (A := A) n * hodgeLaplacian n = hodgeLaplacian n ∧
    hodgeLaplacian (A := A) n * cantorTowerProj (n + 1) = cantorTowerProj (n + 1) ∧
    hodgeLaplacian (A := A) n * (1 - hodgeLaplacian n) = 0 := by
  have h_idem := cantorTowerProj_idem (A := A) n
  have h_mat : hodgeLaplacian (A := A) n = mat2 (cantorTowerProj n) 0 0 (cantorTowerProj n) := by
    apply ext_fin2 <;> simp [hodgeLaplacian, wittD, wittDelta, h_idem]
  have h_sq : hodgeLaplacian (A := A) n * hodgeLaplacian n = hodgeLaplacian n := by
    rw [h_mat]; apply ext_fin2 <;> simp [h_idem]
  refine ⟨?_, h_mat, h_sq, ?_, ?_⟩
  · apply ext_fin2 <;> simp [hodgeLaplacian, wittD, wittDelta, h_idem]
  · rw [h_mat]; apply ext_fin2 <;> simp [cantorTowerProj, h_idem]
  · calc hodgeLaplacian (A := A) n * (1 - hodgeLaplacian n)
      _ = hodgeLaplacian n - hodgeLaplacian n * hodgeLaplacian n := by noncomm_ring
      _ = 0 := by rw [h_sq, sub_self]

theorem hodgeLaplacian_selfAdjoint [StarRing A] (n : ℕ) :
    star (hodgeLaplacian (A := A) n) = hodgeLaplacian n := by
  have h_lap := all_scales_hodge_laplacian_spectral_gap (A := A) n
  have h_proj := (all_scales_inductive_clifford_cantor_fup (A := A) n).2.1
  rw [h_lap.2.1]
  apply ext_fin2 <;> simp [mat2, h_proj]

end ArchetypeMG3_AllScalesHodgeLaplacian

/-!
## Archetype $\mathcal{M}\mathcal{G}_4$: All-Scales Spectral Mass Gap Hamiltonian & $(2^n - 1)$ Excited Pore FUP Law
-/

section ArchetypeMG4_SpectralMassGapAndExcitedPoreFUP

variable [StarRing A]

/-- All-scales gapped Hamiltonian $H_{\mathrm{YM}}^{(n)}(\mu, \lambda) = \mu \bullet 1 + \lambda \bullet (1 - \Pi_{\mathcal{C}_n})$. -/
def massGapHamiltonian (n : ℕ) (μ lam : ℕ) : ClTower n A :=
  μ • (1 : ClTower n A) + lam • (1 - cantorTowerProj n)

/-- **All-Scales Algebraic Mass Split & $(2^n - 1)$ Excited Pore Identity ($\mathcal{M}\mathcal{G}_4$)**:
For every scale $n \in \mathbb{N}$ and mass parameters $\mu, \lambda \in \mathbb{N}$:
1. $H_{\mathrm{YM}}^{(n)}(\mu, \lambda)\,\Pi_{\mathcal{C}_n} = \mu \bullet \Pi_{\mathcal{C}_n}$ (vacuum mass $\mu$) and
   $H_{\mathrm{YM}}^{(n)}(\mu, \lambda)\,(1 - \Pi_{\mathcal{C}_n}) = (\mu + \lambda) \bullet (1 - \Pi_{\mathcal{C}_n})$ (excited mass $\mu + \lambda$),
2. $(H_{\mathrm{YM}}^{(n)}(\mu, \lambda) - \mu \bullet 1)(H_{\mathrm{YM}}^{(n)}(\mu, \lambda) - (\mu + \lambda) \bullet 1) = 0$,
3. *Star-Norm-Square Difference Identity* (no order or positivity structure on `A` is assumed):
   $(H_{\mathrm{YM}}^{(n)})^\star H_{\mathrm{YM}}^{(n)} - (\mu^2) \bullet 1 = (2\mu\lambda + \lambda^2) \bullet ((1 - \Pi_{\mathcal{C}_n})^\star (1 - \Pi_{\mathcal{C}_n}))$,
4. *All-Scales $(2^n - 1)$ Excited Pore FUP Energy Law*:
   $((1 - \Pi_{\mathcal{C}_n})\,\mathcal{U}_n\,\Pi_{\mathcal{C}_n})^\star ((1 - \Pi_{\mathcal{C}_n})\,\mathcal{U}_n\,\Pi_{\mathcal{C}_n}) = (2^n - 1) \bullet \Pi_{\mathcal{C}_n}$. -/
theorem all_scales_mass_gap_hamiltonian_and_excited_pore_fup (n μ lam : ℕ) :
    let P_n := (cantorTowerProj n : ClTower n A)
    let Q_n := 1 - P_n
    let H_n := massGapHamiltonian (A := A) n μ lam
    let U_n := (cayleyTowerOp n : ClTower n A)
    H_n * P_n = μ • P_n ∧
    H_n * Q_n = (μ + lam) • Q_n ∧
    (H_n - μ • 1) * (H_n - (μ + lam) • 1) = 0 ∧
    star H_n * H_n - (μ * μ) • (1 : ClTower n A) =
      (2 * μ * lam + lam * lam) • (star Q_n * Q_n) ∧
    star (Q_n * U_n * P_n) * (Q_n * U_n * P_n) = (2 ^ n - 1) • P_n := by
  intro P_n Q_n H_n U_n
  rcases all_scales_inductive_clifford_cantor_fup (A := A) n with
    ⟨hP_idem, hP_sa_raw, hU_unit_raw, h_comp_raw, _, _⟩
  have hP_sa : star P_n = P_n := hP_sa_raw
  have hU_unit : star U_n * U_n = (2 ^ n) • (1 : ClTower n A) := hU_unit_raw
  have h_comp : P_n * U_n * P_n = P_n := h_comp_raw
  have hQ_idem : Q_n * Q_n = Q_n := by
    dsimp [Q_n]
    calc (1 - P_n) * (1 - P_n) = 1 - P_n - P_n + P_n * P_n := by noncomm_ring
      _ = 1 - P_n := by rw [hP_idem]; noncomm_ring
  have hQ_sa : star Q_n = Q_n := by
    dsimp [Q_n]; rw [star_sub, star_one, hP_sa]
  have hQP : Q_n * P_n = 0 := by
    dsimp [Q_n]
    calc (1 - P_n) * P_n = P_n - P_n * P_n := by noncomm_ring
      _ = 0 := by rw [hP_idem, sub_self]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [H_n, massGapHamiltonian]
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hQP, smul_zero, add_zero]
  · dsimp [H_n, massGapHamiltonian]
    rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hQ_idem, ← add_smul]
  · dsimp [H_n, massGapHamiltonian]
    rw [add_sub_cancel_left, add_smul, sub_add_eq_sub_sub, add_sub_cancel_left, ← smul_sub]
    rw [smul_mul_assoc, mul_smul_comm, ← mul_smul]
    have hQQ1 : Q_n * (Q_n - 1) = 0 := by
      rw [mul_sub, mul_one, hQ_idem, sub_self]
    rw [hQQ1, smul_zero]
  · have hH_sa : star H_n = H_n := by
      dsimp [H_n, massGapHamiltonian]
      rw [star_add, star_nsmul, star_nsmul, star_one, hQ_sa]
    rw [hH_sa, hQ_sa]
    dsimp [H_n, massGapHamiltonian]
    have h_sq : (μ • (1 : ClTower n A) + lam • Q_n) * (μ • (1 : ClTower n A) + lam • Q_n) =
        (μ * μ) • (1 : ClTower n A) + (2 * μ * lam + lam * lam) • (Q_n * Q_n) := by
      rw [add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
          smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
          one_mul, one_mul, mul_one, ← mul_smul, ← mul_smul, ← mul_smul, ← mul_smul,
          hQ_idem, add_assoc]
      have h_coeff : (μ * lam) • Q_n + ((lam * μ) • Q_n + (lam * lam) • Q_n) =
          (2 * μ * lam + lam * lam) • Q_n := by
        rw [← add_smul, ← add_smul]
        congr 1
        ring
      rw [h_coeff]
    rw [h_sq, add_sub_cancel_left]
  · have h_full : star (U_n * P_n) * (U_n * P_n) = (2 ^ n) • P_n := by
      calc star (U_n * P_n) * (U_n * P_n)
        _ = P_n * (star U_n * U_n) * P_n := by simp only [star_mul, hP_sa]; noncomm_ring
        _ = P_n * ((2 ^ n) • 1) * P_n := by rw [hU_unit]
        _ = (2 ^ n) • (P_n * P_n) := by rw [mul_smul_comm, smul_mul_assoc, mul_one]
        _ = (2 ^ n) • P_n := by rw [hP_idem]
    have h_part : star (Q_n * U_n * P_n) * (Q_n * U_n * P_n) +
                  star (P_n * U_n * P_n) * (P_n * U_n * P_n) =
                  star (U_n * P_n) * (U_n * P_n) := by
      simp only [star_mul, hP_sa, hQ_sa]
      calc P_n * (star U_n * Q_n) * (Q_n * U_n * P_n) +
           P_n * (star U_n * P_n) * (P_n * U_n * P_n)
        _ = P_n * star U_n * (Q_n * Q_n) * U_n * P_n +
            P_n * star U_n * (P_n * P_n) * U_n * P_n := by noncomm_ring
        _ = P_n * star U_n * (Q_n + P_n) * U_n * P_n := by rw [hQ_idem, hP_idem]; noncomm_ring
        _ = P_n * star U_n * 1 * U_n * P_n := by dsimp [Q_n]; rw [sub_add_cancel]
        _ = P_n * star U_n * (U_n * P_n) := by noncomm_ring
    rw [h_comp, hP_sa, hP_idem, h_full] at h_part
    have h_pow_split : (2 ^ n) • P_n = (2 ^ n - 1) • P_n + P_n := by
      have h_ge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      calc (2 ^ n) • P_n = ((2 ^ n - 1) + 1) • P_n := by rw [Nat.sub_add_cancel h_ge]
        _ = (2 ^ n - 1) • P_n + P_n := by rw [add_nsmul, one_nsmul]
    rw [h_pow_split] at h_part
    exact add_right_cancel h_part

end ArchetypeMG4_SpectralMassGapAndExcitedPoreFUP

/-!
## Hodge–Parabolic Tower: Nilpotent Monodromy, Vacuum Evacuation & Trace Winding
-/

section HodgeParabolicTower

def hodgeSigma (n : ℕ) : ClTower (n + 1) A := wittD n + wittDelta n
def hodgeOmega (n : ℕ) : ClTower (n + 1) A := wittDelta n - wittD n
def hodgeGamma (n : ℕ) : ClTower (n + 1) A :=
  wittD n * wittDelta n - wittDelta n * wittD n
def hodgeNilpotent (n : ℕ) : ClTower (n + 1) A := hodgeOmega n - hodgeGamma n
def hodgeMonodromy (n : ℕ) : ClTower (n + 1) A := 1 + hodgeNilpotent n

theorem hodgeNilpotent_explicit (n : ℕ) :
    hodgeNilpotent (A := A) n =
      mat2 (-cantorTowerProj n) (-cantorTowerProj n)
        (cantorTowerProj n) (cantorTowerProj n) := by
  have hP := cantorTowerProj_idem (A := A) n
  apply ext_fin2 <;> simp [hodgeNilpotent, hodgeOmega, hodgeGamma, wittD, wittDelta, hP]

theorem hodgeNilpotent_sq_zero (n : ℕ) :
    hodgeNilpotent (A := A) n * hodgeNilpotent n = 0 := by
  have hP := cantorTowerProj_idem (A := A) n
  rw [hodgeNilpotent_explicit]
  apply ext_fin2 <;> simp [hP]

theorem hodgeMonodromy_pow (n k : ℕ) :
    (hodgeMonodromy (A := A) n) ^ k = 1 + k • hodgeNilpotent n := by
  induction' k with m ih
  · simp
  · rw [pow_succ, ih, hodgeMonodromy, add_nsmul, one_nsmul]
    have h_mul : (m • (hodgeNilpotent (A := A) n)) * hodgeNilpotent n = 0 := by
      rw [nsmul_eq_mul, mul_assoc, hodgeNilpotent_sq_zero n, mul_zero]
    calc (1 + m • (hodgeNilpotent (A := A) n)) * (1 + hodgeNilpotent n)
        = 1 + (m • hodgeNilpotent n + hodgeNilpotent n) +
          (m • hodgeNilpotent n) * hodgeNilpotent n := by noncomm_ring
      _ = 1 + (m • hodgeNilpotent n + hodgeNilpotent n) := by rw [h_mul, add_zero]

theorem hodge_parabolic_generator_properties (n k : ℕ) :
    let N := hodgeNilpotent (A := A) n
    let S := hodgeSigma (A := A) n
    let eHarm := 1 - (wittD n * wittDelta n + wittDelta n * wittD n)
    N * N = 0 ∧ S * N * S = -N ∧ N * eHarm = 0 ∧
      (hodgeMonodromy (A := A) n) ^ k = 1 + k • N := by
  have hP := cantorTowerProj_idem (A := A) n
  refine ⟨hodgeNilpotent_sq_zero n, ?_, ?_, hodgeMonodromy_pow n k⟩
  · rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [hodgeSigma, wittD, wittDelta, hP]
  · rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [wittD, wittDelta] <;> noncomm_ring [hP]

theorem hodge_vacuum_evacuation_and_coexact_excitation (n k : ℕ) :
    let P := cantorTowerProj (n + 1)
    let eCo := wittDelta (A := A) n * wittD n
    hodgeMonodromy n * P = wittDelta n ∧
      P * hodgeMonodromy n * P = 0 ∧
      eCo * (hodgeMonodromy n ^ k) * P = k • wittDelta n := by
  have hP := cantorTowerProj_idem (A := A) n
  refine ⟨?_, ?_, ?_⟩
  · dsimp [hodgeMonodromy]
    rw [hodgeNilpotent_explicit]
    (apply ext_fin2 <;> simp [cantorTowerProj, wittDelta, hP])
    rw [add_mul, one_mul, neg_mul, hP, add_neg_cancel]
  · dsimp [hodgeMonodromy]
    rw [hodgeNilpotent_explicit]
    (apply ext_fin2 <;> simp [cantorTowerProj])
    rw [mul_add, mul_one, mul_neg, hP, add_neg_cancel, zero_mul]
  · rw [hodgeMonodromy_pow n k]
    have h_split : (wittDelta (A := A) n * wittD n) *
        (1 + k • hodgeNilpotent (A := A) n) * cantorTowerProj (n + 1) =
        (wittDelta n * wittD n) * cantorTowerProj (n + 1) +
        k • ((wittDelta n * wittD n) * hodgeNilpotent n * cantorTowerProj (n + 1)) := by
      rw [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc]
    have h1 : (wittDelta (A := A) n * wittD n) * cantorTowerProj (n + 1) = 0 := by
      apply ext_fin2 <;> simp [wittDelta, wittD, cantorTowerProj]
    have h2 : (wittDelta (A := A) n * wittD n) * hodgeNilpotent n * cantorTowerProj (n + 1) =
        wittDelta n := by
      rw [hodgeNilpotent_explicit]
      apply ext_fin2 <;> simp [wittDelta, wittD, cantorTowerProj, hP]
    rw [h_split, h1, h2, zero_add]

section HodgeParabolicEnergy

variable [StarRing A]

theorem hodge_k_step_coexact_energy_decomposition (n k : ℕ) :
    let P := cantorTowerProj (n + 1)
    let eCo := wittDelta (A := A) n * wittD n
    let Qk := (hodgeMonodromy (A := A) n) ^ k
    star (eCo * Qk * P) * (eCo * Qk * P) = (k * k) • P ∧
      star (Qk * P) * (Qk * P) =
        star (P * Qk * P) * (P * Qk * P) + (k * k) • P := by
  intro P eCo Qk
  have hP_idem := cantorTowerProj_idem (A := A) n
  have hP_sa := (all_scales_inductive_clifford_cantor_fup (A := A) n).2.1
  have hCo := (hodge_vacuum_evacuation_and_coexact_excitation (A := A) n k).2.2
  have hDelSq : star (wittDelta (A := A) n) * wittDelta n = P := by
    apply ext_fin2 <;> simp [P, wittDelta, cantorTowerProj, hP_sa, hP_idem]
  have hLeak : star (eCo * Qk * P) * (eCo * Qk * P) = (k * k) • P := by
    change star (eCo * ((hodgeMonodromy (A := A) n) ^ k) * P) *
      (eCo * ((hodgeMonodromy (A := A) n) ^ k) * P) = (k * k) • P
    rw [hCo, star_nsmul, smul_mul_assoc, mul_smul_comm, hDelSq, smul_smul]
  refine ⟨hLeak, ?_⟩
  rw [← hLeak]
  have hCo' : eCo * Qk * P = k • wittDelta n := hCo
  have hDecomp : Qk * P = P * Qk * P + k • wittDelta (A := A) n := by
    dsimp [Qk, P]
    rw [hodgeMonodromy_pow n k]
    have hL : (1 + k • hodgeNilpotent (A := A) n) * cantorTowerProj (n + 1) =
        cantorTowerProj (n + 1) + k • (hodgeNilpotent n * cantorTowerProj (n + 1)) := by
      rw [add_mul, one_mul, smul_mul_assoc]
    have hR : cantorTowerProj (A := A) (n + 1) * (1 + k • hodgeNilpotent n) * cantorTowerProj (n + 1) =
        cantorTowerProj (n + 1) + k • (cantorTowerProj (n + 1) * hodgeNilpotent n * cantorTowerProj (n + 1)) := by
      rw [mul_add, mul_one, mul_smul_comm, add_mul, smul_mul_assoc, cantorTowerProj_idem (n + 1)]
    rw [hL, hR, add_assoc]
    congr 1
    rw [← smul_add]
    congr 1
    rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [cantorTowerProj, wittDelta, hP_idem]
  have hOrth1 : star (P * Qk * P) * (k • wittDelta (A := A) n) = 0 := by
    rw [mul_smul_comm]
    have h0 : star (P * Qk * P) * wittDelta (A := A) n = 0 := by
      dsimp [P]
      apply ext_fin2 <;> simp [cantorTowerProj, wittDelta]
    rw [h0, smul_zero]
  have hOrth2 : star (k • wittDelta (A := A) n) * (P * Qk * P) = 0 := by
    rw [star_nsmul, smul_mul_assoc]
    have h0 : star (wittDelta (A := A) n) * (P * Qk * P) = 0 := by
      dsimp [P]
      apply ext_fin2 <;> simp [cantorTowerProj, wittDelta]
    rw [h0, smul_zero]
  rw [hDecomp, star_add, mul_add, add_mul, add_mul, hOrth1, hOrth2, hCo']
  abel

end HodgeParabolicEnergy

lemma superTrace_one_succ (n : ℕ) :
    superTrace (A := A) (1 : ClTower (n + 1) A) = 0 := by
  dsimp [superTrace, gammaTowerOp, towerTrace, rgTowerDecimate]
  simp only [mul_one, mat2_00, mat2_11]
  rw [towerTrace_add, towerTrace_neg]
  abel

theorem hodge_parabolic_trace_winding (n k : ℕ) :
    towerTrace (n + 1) (hodgeNilpotent (A := A) n) = 0 ∧
      superTrace (hodgeNilpotent n) = -(2 • (1 : A)) ∧
      superTrace ((hodgeMonodromy n) ^ k) = -((2 * k) • (1 : A)) := by
  have hSuperN : superTrace (hodgeNilpotent (A := A) n) = -(2 • (1 : A)) := by
    rw [hodgeNilpotent_explicit]
    dsimp [superTrace, gammaTowerOp, towerTrace, rgTowerDecimate]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, mat2_00, mat2_01, mat2_10, mat2_11,
      zero_mul, add_zero, mul_neg, neg_mul,
      gammaTowerOp_cantorTowerProj, towerTrace_add, towerTrace_neg,
      towerTrace_zero, towerTrace_cantor_normalization, two_smul]
    abel
  refine ⟨?_, hSuperN, ?_⟩
  · rw [hodgeNilpotent_explicit]
    dsimp [towerTrace, rgTowerDecimate]
    rw [towerTrace_add, towerTrace_neg]
    abel
  · rw [hodgeMonodromy_pow n k]
    change towerTrace (n + 1) (gammaTowerOp (A := A) (n + 1) *
      (1 + k • hodgeNilpotent (A := A) n)) = -((2 * k) • (1 : A))
    have h_expand : gammaTowerOp (A := A) (n + 1) *
        (1 + k • hodgeNilpotent (A := A) n) =
        gammaTowerOp (A := A) (n + 1) +
          k • (gammaTowerOp (A := A) (n + 1) * hodgeNilpotent (A := A) n) := by
      rw [mul_add, mul_one, mul_smul_comm]
    rw [h_expand, towerTrace_add]
    have h_unit_trace : towerTrace (n + 1) (gammaTowerOp (A := A) (n + 1)) = 0 := by
      simpa [superTrace] using superTrace_one_succ (A := A) n
    rw [h_unit_trace, zero_add]
    rw [towerTrace_nsmul]
    change k • superTrace (hodgeNilpotent (A := A) n) = -((2 * k) • (1 : A))
    rw [hSuperN]
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    noncomm_ring

end HodgeParabolicTower

end InfoGeometry.Algebra.NoncommutativeColimitAndSpectralGapSynthesis
