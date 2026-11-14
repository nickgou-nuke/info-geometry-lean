/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

open Matrix

namespace InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis

/-!
## Foundational Infrastructure: `mat2` Constructor & Simp Lemmas
-/

def mat2 {A : Type*} (a b c d : A) : Matrix (Fin 2) (Fin 2) A :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => a
    | 0, 1 => b
    | 1, 0 => c
    | 1, 1 => d

private theorem matrix2_noncomm_witness {A : Type*} [Ring A] [Nontrivial A] :
    ∃ X Y : Matrix (Fin 2) (Fin 2) A, X * Y ≠ Y * X := by
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

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

@[simp] lemma star2_00 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 0 = star (M 0 0) := rfl
@[simp] lemma star2_01 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 0 1 = star (M 1 0) := rfl
@[simp] lemma star2_10 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 0 = star (M 0 1) := rfl
@[simp] lemma star2_11 {A : Type*} [Star A] (M : Matrix (Fin 2) (Fin 2) A) : (star M) 1 1 = star (M 1 1) := rfl

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

end Matrix2Simp

/-!
## Inductive Tower `ClTower A n` & Core Operators
-/

universe u

@[reducible] def ClTower (A : Type u) : ℕ → Type u
  | 0     => A
  | n + 1 => Matrix (Fin 2) (Fin 2) (ClTower A n)

@[reducible] instance instRingClTower {A : Type u} [Ring A] : ∀ n : ℕ, Ring (ClTower A n)
  | 0     => inferInstanceAs (Ring A)
  | n + 1 =>
      let _ : Ring (ClTower A n) := instRingClTower n
      inferInstanceAs (Ring (Matrix (Fin 2) (Fin 2) (ClTower A n)))

private theorem cltower_noncomm_witness {A : Type u} [Ring A] [Nontrivial A] (n : ℕ) :
    ∃ X Y : Matrix (Fin 2) (Fin 2) (ClTower A n), X * Y ≠ Y * X := by
  let _ : Ring (ClTower A n) := instRingClTower n
  haveI : Nontrivial (ClTower A n) := by
    induction n with
    | zero => infer_instance
    | succ n ih =>
        let _ : Ring (ClTower A n) := instRingClTower n
        exact ⟨⟨Matrix.of fun _ _ => 0, Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0, by
          intro h
          have h00 := congr_fun (congr_fun h 0) 0
          simp at h00⟩⟩
  refine ⟨Matrix.of fun i j => match i, j with | 0, 1 => 1 | _, _ => 0,
          Matrix.of fun i j => match i, j with | 1, 0 => 1 | _, _ => 0, ?_⟩
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

@[reducible] instance instStarRingClTower {A : Type u} [Ring A] [StarRing A] :
    ∀ n : ℕ, StarRing (ClTower A n)
  | 0     => inferInstanceAs (StarRing A)
  | n + 1 =>
      let _ : Ring (ClTower A n) := instRingClTower n
      let _ : StarRing (ClTower A n) := instStarRingClTower n
      inferInstanceAs (StarRing (Matrix (Fin 2) (Fin 2) (ClTower A n)))

variable {A : Type u} [Ring A]

def cantorProj : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (cantorProj n) 0 0 0

def chiralityOp : ∀ (n : ℕ), ClTower A n
  | 0     => (1 : A)
  | n + 1 => mat2 (chiralityOp n) 0 0 (-chiralityOp n)

def towerTrace : ∀ {n : ℕ}, ClTower A n → A
  | 0,     x => x
  | _ + 1, M => towerTrace (M 0 0) + towerTrace (M 1 1)

def superTrace {n : ℕ} (M : ClTower A n) : A :=
  towerTrace (chiralityOp n * M)

lemma towerTrace_zero : ∀ (n : ℕ), towerTrace (0 : ClTower A n) = 0
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace]
      rw [towerTrace_zero n, add_zero]

lemma towerTrace_add : ∀ {n : ℕ} (X Y : ClTower A n),
    towerTrace (X + Y) = towerTrace X + towerTrace Y
  | 0,     _, _ => rfl
  | _ + 1, X, Y => by
      dsimp [towerTrace]
      rw [towerTrace_add, towerTrace_add]
      abel

lemma towerTrace_neg : ∀ {n : ℕ} (X : ClTower A n), towerTrace (-X) = -towerTrace X
  | 0,     _ => rfl
  | _ + 1, X => by
      dsimp [towerTrace]
      rw [towerTrace_neg, towerTrace_neg]
      abel

lemma towerTrace_nsmul {n : ℕ} (k : ℕ) (X : ClTower A n) :
    towerTrace (k • X) = k • towerTrace X := by
  induction' k with m ih
  · simp [towerTrace_zero n]
  · rw [add_nsmul, one_nsmul, towerTrace_add, ih, add_nsmul, one_nsmul]

lemma cantorProj_idempotent : ∀ (n : ℕ),
    (cantorProj n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_idempotent n]

lemma cantorProj_selfAdjoint [StarRing A] : ∀ (n : ℕ),
    star (cantorProj n : ClTower A n) = cantorProj n
  | 0     => star_one A
  | n + 1 => by apply ext_fin2 <;> simp [cantorProj, cantorProj_selfAdjoint n]

lemma chiralityOp_cantorProj : ∀ (n : ℕ),
    (chiralityOp n : ClTower A n) * cantorProj n = cantorProj n
  | 0     => mul_one 1
  | n + 1 => by apply ext_fin2 <;> simp [chiralityOp, cantorProj, chiralityOp_cantorProj n]

lemma towerTrace_cantorProj : ∀ (n : ℕ),
    towerTrace (cantorProj n : ClTower A n) = 1
  | 0     => rfl
  | n + 1 => by
      dsimp [towerTrace, cantorProj]
      rw [towerTrace_zero n, add_zero, towerTrace_cantorProj n]

/-!
## Archetype $\mathcal{H}\mathcal{P}_1$: All-Scales Hodge–Parabolic Light-Cone Nilpotent Generator $\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$
-/

section ArchetypeHP1_HodgeParabolicGenerator

def wittD (n : ℕ) : ClTower A (n + 1) := mat2 0 (cantorProj n) 0 0
def wittDelta (n : ℕ) : ClTower A (n + 1) := mat2 0 0 (cantorProj n) 0

/-- Local Hodge $Cl(1,1)$ triad inside $\mathcal{C}\ell_{n+1}(A)$. -/
def hodgeSigma (n : ℕ) : ClTower A (n + 1) := wittD n + wittDelta n
def hodgeOmega (n : ℕ) : ClTower A (n + 1) := wittDelta n - wittD n
def hodgeGamma (n : ℕ) : ClTower A (n + 1) := wittD n * wittDelta n - wittDelta n * wittD n

/-- The $(n+1)$-scale Hodge–Parabolic light-cone nilpotent generator
$\mathcal{N}_{\mathrm{Hodge}}^{(n+1)} = \Omega_{\mathrm{Hodge}}^{(n+1)} - \Gamma_{\mathrm{Hodge}}^{(n+1)}$
and monodromy $Q_{\mathrm{Hodge}}^{(n+1)} = 1 + \mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$. -/
def hodgeNilpotent (n : ℕ) : ClTower A (n + 1) :=
  hodgeOmega n - hodgeGamma n

def hodgeMonodromy (n : ℕ) : ClTower A (n + 1) :=
  1 + hodgeNilpotent n

theorem hodgeNilpotent_explicit (n : ℕ) :
    hodgeNilpotent (A := A) n =
      mat2 (-cantorProj n) (-cantorProj n) (cantorProj n) (cantorProj n) := by
  have hP := cantorProj_idempotent (A := A) n
  apply ext_fin2 <;> simp [hodgeNilpotent, hodgeOmega, hodgeGamma, wittD, wittDelta, hP]

theorem hodgeNilpotent_sq_zero (n : ℕ) :
    hodgeNilpotent (A := A) n * hodgeNilpotent n = 0 := by
  have hP := cantorProj_idempotent (A := A) n
  rw [hodgeNilpotent_explicit]
  apply ext_fin2 <;> simp [hP]

theorem hodgeMonodromy_pow (n k : ℕ) :
    (hodgeMonodromy (A := A) n) ^ k = 1 + k • hodgeNilpotent n := by
  induction' k with m ih
  · simp
  · rw [pow_succ, ih, hodgeMonodromy, add_nsmul, one_nsmul]
    have h_mul : (m • hodgeNilpotent (A := A) n) * hodgeNilpotent n = 0 := by
      rw [nsmul_eq_mul, mul_assoc, hodgeNilpotent_sq_zero n, mul_zero]
    calc (1 + m • hodgeNilpotent (A := A) n) * (1 + hodgeNilpotent n)
      _ = 1 + (m • hodgeNilpotent n + hodgeNilpotent n) +
          (m • hodgeNilpotent n) * hodgeNilpotent n := by noncomm_ring
      _ = 1 + (m • hodgeNilpotent n + hodgeNilpotent n) := by rw [h_mul, add_zero]

/-- **All-Scales Hodge–Parabolic Light-Cone Theorem ($\mathcal{H}\mathcal{P}_1$)**:
At every scale $n \in \mathbb{N}$:
1. $(\mathcal{N}_{\mathrm{Hodge}}^{(n+1)})^2 = 0$,
2. $\Sigma_{\mathrm{Hodge}}^{(n+1)} \mathcal{N}_{\mathrm{Hodge}}^{(n+1)} \Sigma_{\mathrm{Hodge}}^{(n+1)} = -\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$,
3. $\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$ annihilates the harmonic projection $1 - (d_n\delta_n + \delta_n d_n)$,
4. $(Q_{\mathrm{Hodge}}^{(n+1)})^k = 1 + k \bullet \mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$ for all $k \in \mathbb{N}$. -/
theorem all_scales_hodge_parabolic_generator_properties (n k : ℕ) :
    let N_n := hodgeNilpotent (A := A) n
    let Sigma_n := hodgeSigma (A := A) n
    let e_harm := 1 - (wittD (A := A) n * wittDelta n + wittDelta n * wittD n)
    N_n * N_n = 0 ∧
    Sigma_n * N_n * Sigma_n = -N_n ∧
    N_n * e_harm = 0 ∧
    (hodgeMonodromy (A := A) n) ^ k = 1 + k • N_n := by
  have hP := cantorProj_idempotent (A := A) n
  refine ⟨hodgeNilpotent_sq_zero n, ?_, ?_, hodgeMonodromy_pow n k⟩
  · rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [hodgeSigma, wittD, wittDelta, hP]
  · rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [wittD, wittDelta, hP, mul_sub]

end ArchetypeHP1_HodgeParabolicGenerator

/-!
## Archetype $\mathcal{H}\mathcal{P}_2$ & $\mathcal{H}\mathcal{P}_3$: 1-Step Total Vacuum Evacuation & $k$-Step Positive-Cone Coexact Leakage
-/

section ArchetypeHP2_HP3_VacuumEvacuationAndCoexactLeakage

/-- **1-Step Total Vacuum Evacuation & $k$-Step Coexact Excitation Theorem ($\mathcal{H}\mathcal{P}_2$)**:
At every scale $n \in \mathbb{N}$:
1. $Q_{\mathrm{Hodge}}^{(n+1)} \Pi_{\mathcal{C}_{n+1}} = \delta_n$ (1-step total evacuation into the coexact Witt sheet),
2. $\Pi_{\mathcal{C}_{n+1}} Q_{\mathrm{Hodge}}^{(n+1)} \Pi_{\mathcal{C}_{n+1}} = 0$ (vanishing 1-step vacuum survival),
3. $(\delta_n d_n) (Q_{\mathrm{Hodge}}^{(n+1)})^k \Pi_{\mathcal{C}_{n+1}} = k \bullet \delta_n$ ($k$-step coexact excitation law). -/
theorem vacuum_evacuation_and_k_step_coexact_excitation (n k : ℕ) :
    let P_vac := cantorProj (A := A) (n + 1)
    let e_co  := wittDelta (A := A) n * wittD n
    hodgeMonodromy n * P_vac = wittDelta n ∧
    P_vac * hodgeMonodromy n * P_vac = 0 ∧
    e_co * ((hodgeMonodromy n) ^ k) * P_vac = k • wittDelta n := by
  have hP := cantorProj_idempotent (A := A) n
  refine ⟨?_, ?_, ?_⟩
  · dsimp [hodgeMonodromy]
    rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [cantorProj, wittDelta, hP]
    rw [add_mul, one_mul, neg_mul, hP, add_neg_cancel]
  · dsimp [hodgeMonodromy]
    rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [cantorProj, hP]
    rw [mul_add, mul_one, mul_neg, hP, add_neg_cancel, zero_mul]
  · rw [hodgeMonodromy_pow n k]
    have h_split : (wittDelta (A := A) n * wittD n) *
        (1 + k • hodgeNilpotent (A := A) n) * cantorProj (n + 1) =
        (wittDelta n * wittD n) * cantorProj (n + 1) +
        k • ((wittDelta n * wittD n) * hodgeNilpotent n * cantorProj (n + 1)) := by
      rw [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc]
    have h1 : (wittDelta (A := A) n * wittD n) * cantorProj (n + 1) = 0 := by
      apply ext_fin2 <;> simp [wittDelta, wittD, cantorProj]
    have h2 : (wittDelta (A := A) n * wittD n) * hodgeNilpotent n * cantorProj (n + 1) =
        wittDelta n := by
      rw [hodgeNilpotent_explicit]
      apply ext_fin2 <;> simp [wittDelta, wittD, cantorProj, hP]
    rw [h_split, h1, h2, zero_add]

variable [StarRing A]

/-- **$k$-Step Quadratic Coexact Leakage & Positive-Cone Energy Decomposition ($\mathcal{H}\mathcal{P}_3$)**:
Over any noncommutative $\star$-ring $A$, at every scale $n \in \mathbb{N}$ and step $k \in \mathbb{N}$:
1. The Hermitian square of the coexact excitation $e_{\mathrm{co}}^{(n+1)} (Q_{\mathrm{Hodge}}^{(n+1)})^k \Pi_{\mathcal{C}_{n+1}}$
   is $(k^2) \bullet \Pi_{\mathcal{C}_{n+1}}$,
2. The total $k$-step parabolic state energy decomposes into the vacuum survival energy plus $(k^2) \bullet \Pi_{\mathcal{C}_{n+1}}$. -/
theorem k_step_coexact_leakage_and_positive_cone_energy (n k : ℕ) :
    let P_vac := cantorProj (A := A) (n + 1)
    let e_co  := wittDelta (A := A) n * wittD n
    let Q_k   := (hodgeMonodromy (A := A) n) ^ k
    star (e_co * Q_k * P_vac) * (e_co * Q_k * P_vac) = (k * k) • P_vac ∧
    star (Q_k * P_vac) * (Q_k * P_vac) =
      star (P_vac * Q_k * P_vac) * (P_vac * Q_k * P_vac) + (k * k) • P_vac := by
  intro P_vac e_co Q_k
  have hP_idem := cantorProj_idempotent (A := A) n
  have hP_sa   := cantorProj_selfAdjoint (A := A) n
  have h_co    := (vacuum_evacuation_and_k_step_coexact_excitation (A := A) n k).2.2
  have h_del_sq : star (wittDelta (A := A) n) * wittDelta n = P_vac := by
    apply ext_fin2 <;> simp [P_vac, wittDelta, cantorProj, hP_sa, hP_idem]
  have h_leak : star (e_co * Q_k * P_vac) * (e_co * Q_k * P_vac) = (k * k) • P_vac := by
    change star (e_co * ((hodgeMonodromy (A := A) n) ^ k) * P_vac) *
      (e_co * ((hodgeMonodromy (A := A) n) ^ k) * P_vac) = (k * k) • P_vac
    rw [h_co, star_nsmul, smul_mul_assoc, mul_smul_comm, h_del_sq, smul_smul]
  refine ⟨h_leak, ?_⟩
  rw [← h_leak]
  have h_co' : e_co * Q_k * P_vac = k • wittDelta n := h_co
  have h_decomp : Q_k * P_vac = P_vac * Q_k * P_vac + k • wittDelta n := by
    dsimp [Q_k, P_vac]
    rw [hodgeMonodromy_pow n k]
    have hL : (1 + k • hodgeNilpotent (A := A) n) * cantorProj (n + 1) =
        cantorProj (n + 1) + k • (hodgeNilpotent n * cantorProj (n + 1)) := by
      rw [add_mul, one_mul, smul_mul_assoc]
    have hR : cantorProj (A := A) (n + 1) * (1 + k • hodgeNilpotent n) * cantorProj (n + 1) =
        cantorProj (n + 1) + k • (cantorProj (n + 1) * hodgeNilpotent n * cantorProj (n + 1)) := by
      rw [mul_add, mul_one, mul_smul_comm, add_mul, smul_mul_assoc, cantorProj_idempotent (n + 1)]
    rw [hL, hR, add_assoc]
    congr 1
    rw [← smul_add]
    congr 1
    rw [hodgeNilpotent_explicit]
    apply ext_fin2 <;> simp [cantorProj, wittDelta, hP_idem]
  have h_orth1 : star (P_vac * Q_k * P_vac) * (k • wittDelta n) = 0 := by
    rw [mul_smul_comm]
    have h0 : star (P_vac * Q_k * P_vac) * wittDelta n = 0 := by
      dsimp [P_vac]
      apply ext_fin2 <;> simp [cantorProj, wittDelta]
    rw [h0, smul_zero]
  have h_orth2 : star (k • wittDelta n) * (P_vac * Q_k * P_vac) = 0 := by
    rw [star_nsmul, smul_mul_assoc]
    have h0 : star (wittDelta n) * (P_vac * Q_k * P_vac) = 0 := by
      dsimp [P_vac]
      apply ext_fin2 <;> simp [cantorProj, wittDelta]
    rw [h0, smul_zero]
  rw [h_decomp, star_add, mul_add, add_mul, add_mul, h_orth1, h_orth2, h_co']
  abel

end ArchetypeHP2_HP3_VacuumEvacuationAndCoexactLeakage

/-!
## Archetype $\mathcal{H}\mathcal{P}_4$: All-Scales Trace Blindness vs. Atiyah–Singer Supertrace Winding Detection
-/

section ArchetypeHP4_TraceBlindnessVsSupertraceWinding

theorem superTrace_one_succ (n : ℕ) :
    superTrace (1 : ClTower A (n + 1)) = 0 := by
  dsimp [superTrace, chiralityOp, towerTrace]
  simp [towerTrace_neg]

/-- **All-Scales Trace Blindness vs. Supertrace Winding Detection Theorem ($\mathcal{H}\mathcal{P}_4$)**:
At every scale $n \in \mathbb{N}$ and parabolic step $k \in \mathbb{N}$:
1. $\mathrm{Tr}_{2^{n+1}}(\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}) = 0$ (ungraded trace is blind to $\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}$),
2. $\mathrm{Str}_{2^{n+1}}(\mathcal{N}_{\mathrm{Hodge}}^{(n+1)}) = -(2 \bullet 1_A)$,
3. $\mathrm{Str}_{2^{n+1}}\big((Q_{\mathrm{Hodge}}^{(n+1)})^k\big) = -((2 * k) \bullet 1_A)$ (supertrace detects the exact winding $k$). -/
theorem all_scales_trace_blindness_vs_supertrace_winding_detection (n k : ℕ) :
    towerTrace (hodgeNilpotent (A := A) n) = 0 ∧
    superTrace (hodgeNilpotent (A := A) n) = -(2 • (1 : A)) ∧
    superTrace ((hodgeMonodromy (A := A) n) ^ k) = -((2 * k) • (1 : A)) := by
  have h_super_nil : superTrace (hodgeNilpotent (A := A) n) = -(2 • (1 : A)) := by
    dsimp [superTrace]
    rw [hodgeNilpotent_explicit]
    dsimp [chiralityOp, towerTrace]
    simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      zero_mul, add_zero, mul_neg, neg_mul, neg_zero, zero_add,
      chiralityOp_cantorProj n, towerTrace_neg, towerTrace_cantorProj n, two_smul]
    abel
  refine ⟨?_, h_super_nil, ?_⟩
  · rw [hodgeNilpotent_explicit]
    dsimp [towerTrace]
    simp [towerTrace_neg]
  · rw [hodgeMonodromy_pow n k]
    dsimp [superTrace]
    have h_lin : chiralityOp (n + 1) * (1 + k • hodgeNilpotent (A := A) n) =
        chiralityOp (n + 1) * 1 + k • (chiralityOp (n + 1) * hodgeNilpotent n) := by
      rw [mul_add, mul_smul_comm]
    rw [h_lin, towerTrace_add, towerTrace_nsmul]
    change superTrace (1 : ClTower A (n + 1)) +
           k • superTrace (hodgeNilpotent (A := A) n) = -((2 * k) • (1 : A))
    rw [superTrace_one_succ n, zero_add, h_super_nil]
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    noncomm_ring

end ArchetypeHP4_TraceBlindnessVsSupertraceWinding

end InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis
