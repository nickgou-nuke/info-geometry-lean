/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge
import InfoGeometry.Nuclear.NuclearPhononRPAAlgebra

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Physics.NuclearPhononRPA

/-!
# RPA Quasiboson Phonon Algebra & Quasiparticle Coupling

This module formalizes the collective phonon excitation layer under the RPA / quasiboson approximation:
1. **The RPA Bosonic Algebra**:
   $[Q_i, Q_j] = 0$, $[Q_i^\dagger, Q_j^\dagger] = 0$, $[Q_i, Q_j^\dagger] = \delta_{ij} \cdot 1$.
2. **Harmonic Phonon Hamiltonian**:
   $H_{\text{phonon}} = \sum_i \omega_i Q_i^\dagger Q_i$.
3. **Phonon Creation Commutator**:
   $[H_{\text{phonon}}, Q_k^\dagger] = \omega_k Q_k^\dagger$.
4. **Quasiparticle-Phonon Cross-Commutators**:
   $[Q_i, \alpha_j^\dagger] = 0$, $[Q_i^\dagger, \alpha_j^\dagger] = 0$ (independent collective degrees of freedom).

All proofs are complete in native Lean 4 with 0 `sorry`s.
-/

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Associative commutator. -/
def comm (X Y : A) : A := X * Y - Y * X

/-- The RPA Quasiboson Phonon algebra structure. -/
structure PhononRPA (ι : Type*) [DecidableEq ι] (A : Type*) [Ring A] where
  Q : ι → A
  Qdag : ι → A
  comm_Q_Q : ∀ i j, comm (Q i) (Q j) = 0
  comm_Qdag_Qdag : ∀ i j, comm (Qdag i) (Qdag j) = 0
  comm_Q_Qdag : ∀ i j, comm (Q i) (Qdag j) = if i = j then 1 else 0

namespace PhononRPA

variable (rpa : PhononRPA ι A)

/-- Phonon number operator: $M_i = Q_i^\dagger Q_i$. -/
def numberOp (i : ι) : A :=
  rpa.Qdag i * rpa.Q i

omit [Algebra ℝ A] in
/-- **Theorem**: Number-Creation commutator: $[M_i, Q_i^\dagger] = Q_i^\dagger$. -/
theorem comm_numberOp_Qdag_same (i : ι) :
    comm (rpa.numberOp i) (rpa.Qdag i) = rpa.Qdag i := by
  dsimp [comm, numberOp]
  have h_comm : rpa.Q i * rpa.Qdag i = 1 + rpa.Qdag i * rpa.Q i := by
    have h := rpa.comm_Q_Qdag i i
    simp only [ite_true, comm] at h
    rw [sub_eq_iff_eq_add] at h
    exact h
  calc rpa.Qdag i * rpa.Q i * rpa.Qdag i - rpa.Qdag i * (rpa.Qdag i * rpa.Q i)
      = rpa.Qdag i * (rpa.Q i * rpa.Qdag i) - (rpa.Qdag i * rpa.Qdag i) * rpa.Q i := by
        simp only [mul_assoc]
    _ = rpa.Qdag i * (1 + rpa.Qdag i * rpa.Q i) - (rpa.Qdag i * rpa.Qdag i) * rpa.Q i := by
        rw [h_comm]
    _ = (rpa.Qdag i * 1 + rpa.Qdag i * (rpa.Qdag i * rpa.Q i)) - (rpa.Qdag i * rpa.Qdag i) * rpa.Q i := by
        rw [mul_add]
    _ = (rpa.Qdag i + (rpa.Qdag i * rpa.Qdag i) * rpa.Q i) - (rpa.Qdag i * rpa.Qdag i) * rpa.Q i := by
        simp only [mul_one, mul_assoc]
    _ = rpa.Qdag i := by
        rw [add_sub_cancel_right]

omit [Algebra ℝ A] in
/-- **Theorem**: Number-Creation commutator for distinct modes: $[M_i, Q_j^\dagger] = 0$. -/
theorem comm_numberOp_Qdag_distinct (i j : ι) (hij : i ≠ j) :
    comm (rpa.numberOp i) (rpa.Qdag j) = 0 := by
  dsimp [comm, numberOp]
  have h_comm_Q : rpa.Q i * rpa.Qdag j = rpa.Qdag j * rpa.Q i := by
    have h := rpa.comm_Q_Qdag i j
    simp only [hij, ite_false, comm] at h
    rw [sub_eq_zero] at h
    exact h
  have h_comm_Qdag : rpa.Qdag i * rpa.Qdag j = rpa.Qdag j * rpa.Qdag i := by
    have h := rpa.comm_Qdag_Qdag i j
    dsimp [comm] at h
    rw [sub_eq_zero] at h
    exact h
  calc rpa.Qdag i * rpa.Q i * rpa.Qdag j - rpa.Qdag j * (rpa.Qdag i * rpa.Q i)
      = rpa.Qdag i * (rpa.Q i * rpa.Qdag j) - (rpa.Qdag j * rpa.Qdag i) * rpa.Q i := by
        simp only [mul_assoc]
    _ = rpa.Qdag i * (rpa.Qdag j * rpa.Q i) - (rpa.Qdag i * rpa.Qdag j) * rpa.Q i := by
        rw [h_comm_Q, ← h_comm_Qdag]
    _ = (rpa.Qdag i * rpa.Qdag j) * rpa.Q i - (rpa.Qdag i * rpa.Qdag j) * rpa.Q i := by
        simp only [mul_assoc]
    _ = 0 := by
        rw [sub_self]

/-- Harmonic RPA collective Hamiltonian: $H_{\text{phonon}} = \sum_{i \in s} \omega_i M_i$. -/
def harmonicPhononHamiltonian (s : Finset ι) (omega : ι → ℝ) : A :=
  ∑ i ∈ s, (omega i) • rpa.numberOp i

/-- **Theorem**: Commutator of $H_{\text{phonon}}$ with creation operator:
    $[H_{\text{phonon}}, Q_k^\dagger] = \omega_k Q_k^\dagger$. -/
theorem comm_harmonicPhononHamiltonian_Qdag (s : Finset ι) (omega : ι → ℝ) (k : ι) (hk : k ∈ s) :
    comm (rpa.harmonicPhononHamiltonian s omega) (rpa.Qdag k) = (omega k) • rpa.Qdag k := by
  dsimp [harmonicPhononHamiltonian, comm]
  have h_comm_sum : (∑ i ∈ s, (omega i) • rpa.numberOp i) * rpa.Qdag k -
                    rpa.Qdag k * (∑ i ∈ s, (omega i) • rpa.numberOp i) =
      ∑ i ∈ s, (omega i) • comm (rpa.numberOp i) (rpa.Qdag k) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [comm]
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [h_comm_sum]
  rw [Finset.sum_eq_single k]
  · rw [rpa.comm_numberOp_Qdag_same k]
  · intro j hj hjk
    rw [rpa.comm_numberOp_Qdag_distinct j k hjk, smul_zero]
  · intro hnk
    exact False.elim (hnk hk)

omit [Algebra ℝ A] in
/-- **Theorem**: Number-Annihilation commutator: $[M_i, Q_i] = -Q_i$. -/
theorem comm_numberOp_Q_same (i : ι) :
    comm (rpa.numberOp i) (rpa.Q i) = -rpa.Q i := by
  dsimp [comm, numberOp]
  have h_comm : rpa.Q i * rpa.Qdag i = 1 + rpa.Qdag i * rpa.Q i := by
    have h := rpa.comm_Q_Qdag i i
    simp only [↓reduceIte, comm] at h
    exact sub_eq_iff_eq_add.mp h
  calc rpa.Qdag i * rpa.Q i * rpa.Q i - rpa.Q i * (rpa.Qdag i * rpa.Q i)
      = rpa.Qdag i * (rpa.Q i * rpa.Q i) - (rpa.Q i * rpa.Qdag i) * rpa.Q i := by
        simp only [mul_assoc]
    _ = rpa.Qdag i * (rpa.Q i * rpa.Q i) - (1 + rpa.Qdag i * rpa.Q i) * rpa.Q i := by
        rw [h_comm]
    _ = -rpa.Q i := by noncomm_ring

omit [Algebra ℝ A] in
/-- **Theorem**: Number-Annihilation commutator for distinct modes: $[M_i, Q_j] = 0$. -/
theorem comm_numberOp_Q_distinct (i j : ι) (hij : i ≠ j) :
    comm (rpa.numberOp i) (rpa.Q j) = 0 := by
  dsimp [comm, numberOp]
  have h_comm_Q : rpa.Q i * rpa.Q j = rpa.Q j * rpa.Q i := by
    have h := rpa.comm_Q_Q i j
    dsimp [comm] at h
    exact sub_eq_zero.mp h
  have h_comm_Qdag : rpa.Q j * rpa.Qdag i = rpa.Qdag i * rpa.Q j := by
    have h := rpa.comm_Q_Qdag j i
    simp only [Ne.symm hij, ↓reduceIte, comm] at h
    exact sub_eq_zero.mp h
  calc rpa.Qdag i * rpa.Q i * rpa.Q j - rpa.Q j * (rpa.Qdag i * rpa.Q i)
      = rpa.Qdag i * (rpa.Q i * rpa.Q j) - (rpa.Q j * rpa.Qdag i) * rpa.Q i := by
        simp only [mul_assoc]
    _ = rpa.Qdag i * (rpa.Q j * rpa.Q i) - (rpa.Qdag i * rpa.Q j) * rpa.Q i := by
        rw [h_comm_Q, h_comm_Qdag]
    _ = 0 := by noncomm_ring

/-- **Theorem**: Commutator of $H_{\text{phonon}}$ with annihilation operator:
    $[H_{\text{phonon}}, Q_k] = -\omega_k Q_k$. -/
theorem comm_harmonicPhononHamiltonian_Q (s : Finset ι) (omega : ι → ℝ) (k : ι) (hk : k ∈ s) :
    comm (rpa.harmonicPhononHamiltonian s omega) (rpa.Q k) = -((omega k) • rpa.Q k) := by
  dsimp [harmonicPhononHamiltonian, comm]
  have h_comm_sum : (∑ i ∈ s, (omega i) • rpa.numberOp i) * rpa.Q k -
                    rpa.Q k * (∑ i ∈ s, (omega i) • rpa.numberOp i) =
      ∑ i ∈ s, (omega i) • comm (rpa.numberOp i) (rpa.Q k) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [comm]
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [h_comm_sum, Finset.sum_eq_single k]
  · rw [rpa.comm_numberOp_Q_same k, smul_neg]
  · intro j _ hjk
    rw [rpa.comm_numberOp_Q_distinct j k hjk, smul_zero]
  · intro hnk
    exact False.elim (hnk hk)

/-! ## Finite RPA Eigenmodes & Thouless / Goldstone Zero-Mode Theorem -/

section ThoulessGoldstone

variable {R : Type*} [CommRing R] [Algebra R A]

omit [Algebra ℝ A] in
/-- Collective RPA linear mode $P(x, y) = \sum_{i \in s} (x_i Q_i^\dagger + y_i Q_i)$. -/
def rpaMode (s : Finset ι) (x y : ι → R) : A :=
  ∑ i ∈ s, (x i • rpa.Qdag i + y i • rpa.Q i)

omit [Algebra ℝ A] in
private theorem comm_add_left (X Y Z : A) : comm (X + Y) Z = comm X Z + comm Y Z := by
  dsimp [comm]; noncomm_ring

omit [Algebra ℝ A] in
private theorem comm_add_right (X Y Z : A) : comm X (Y + Z) = comm X Y + comm X Z := by
  dsimp [comm]; noncomm_ring

omit [Algebra ℝ A] in
private theorem comm_sub_right (X Y Z : A) : comm X (Y - Z) = comm X Y - comm X Z := by
  dsimp [comm]; noncomm_ring

omit [Algebra ℝ A] in
private theorem comm_smul_right (r : R) (X Y : A) : comm X (r • Y) = r • comm X Y := by
  dsimp [comm]; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]

omit [Algebra ℝ A] in
private theorem comm_sum_right {β : Type*} (s : Finset β) (X : A) (f : β → A) :
    comm X (∑ i ∈ s, f i) = ∑ i ∈ s, comm X (f i) := by
  dsimp [comm]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

omit [Algebra ℝ A] in
/-- Extracting the forward amplitude $x_k$ via $[Q_k, P(x, y)]$. -/
theorem comm_Q_rpaMode (s : Finset ι) (x y : ι → R) (k : ι) :
    comm (rpa.Q k) (rpa.rpaMode s x y) = (if k ∈ s then x k else 0) • (1 : A) := by
  dsimp [rpaMode]
  rw [comm_sum_right]
  have hterm : ∀ i ∈ s, comm (rpa.Q k) (x i • rpa.Qdag i + y i • rpa.Q i) =
      (if k = i then x i else 0) • (1 : A) := by
    intro i _
    rw [comm_add_right, comm_smul_right, comm_smul_right,
      rpa.comm_Q_Q k i, rpa.comm_Q_Qdag k i, smul_zero, add_zero]
    split_ifs with hki
    · subst hki; simp
    · simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hk : k ∈ s
  · simp only [hk, ↓reduceIte]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      simp [Ne.symm hik]
    · intro hnk; exact False.elim (hnk hk)
  · simp only [hk, ↓reduceIte, zero_smul]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    simp [hki]

omit [Algebra ℝ A] in
/-- Extracting the backward amplitude $-y_k$ via $[Q_k^\dagger, P(x, y)]$. -/
theorem comm_Qdag_rpaMode (s : Finset ι) (x y : ι → R) (k : ι) :
    comm (rpa.Qdag k) (rpa.rpaMode s x y) = (if k ∈ s then -y k else 0) • (1 : A) := by
  dsimp [rpaMode]
  rw [comm_sum_right]
  have hQdag_Q (i j : ι) : comm (rpa.Qdag i) (rpa.Q j) = -(if j = i then (1 : A) else 0) := by
    have h := rpa.comm_Q_Qdag j i
    dsimp [comm] at h ⊢
    rw [← h]
    abel
  have hterm : ∀ i ∈ s, comm (rpa.Qdag k) (x i • rpa.Qdag i + y i • rpa.Q i) =
      (if k = i then -y i else 0) • (1 : A) := by
    intro i _
    rw [comm_add_right, comm_smul_right, comm_smul_right,
      rpa.comm_Qdag_Qdag k i, hQdag_Q k i, smul_zero, zero_add]
    by_cases hki : k = i
    · subst hki; simp [neg_smul]
    · simp [hki, Ne.symm hki]
  rw [Finset.sum_congr rfl hterm]
  by_cases hk : k ∈ s
  · simp only [hk, ↓reduceIte]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      simp [Ne.symm hik]
    · intro hnk; exact False.elim (hnk hk)
  · simp only [hk, ↓reduceIte, zero_smul]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    simp [hki]

omit [Algebra ℝ A] in
private theorem comm_Q_eom_rpaMode (s : Finset ι) (H : A) (A_mat B_mat : ι → ι → R)
    (x y : ι → R) (k : ι) (hk : k ∈ s)
    (h_eom_Qdag : ∀ i ∈ s, comm H (rpa.Qdag i) =
      ∑ j ∈ s, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j))
    (h_eom_Q : ∀ i ∈ s, comm H (rpa.Q i) =
      ∑ j ∈ s, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j)) :
    comm (rpa.Q k) (comm H (rpa.rpaMode s x y)) =
      (∑ i ∈ s, (A_mat k i * x i + B_mat k i * y i)) • (1 : A) := by
  dsimp [rpaMode]
  rw [comm_sum_right, comm_sum_right]
  have hterm : ∀ i ∈ s,
      comm (rpa.Q k) (comm H (x i • rpa.Qdag i + y i • rpa.Q i)) =
        (A_mat k i * x i + B_mat k i * y i) • (1 : A) := by
    intro i hi
    rw [comm_add_right, comm_smul_right, comm_smul_right,
      comm_add_right, comm_smul_right, comm_smul_right,
      h_eom_Qdag i hi, h_eom_Q i hi]
    have h_inner_dag : comm (rpa.Q k)
        (∑ j ∈ s, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j)) =
        A_mat k i • (1 : A) := by
      rw [comm_sum_right]
      have hsub : ∀ j ∈ s,
          comm (rpa.Q k) (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j) =
            (if k = j then A_mat j i else 0) • (1 : A) := by
        intro j _
        rw [comm_sub_right, comm_smul_right, comm_smul_right,
          rpa.comm_Q_Qdag k j, rpa.comm_Q_Q k j, smul_zero, sub_zero]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hsub, Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [Ne.symm hjk]
      · intro hnk; exact False.elim (hnk hk)
    have h_inner_q : comm (rpa.Q k)
        (∑ j ∈ s, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j)) =
        B_mat k i • (1 : A) := by
      rw [comm_sum_right]
      have hsub : ∀ j ∈ s,
          comm (rpa.Q k) (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j) =
            (if k = j then B_mat j i else 0) • (1 : A) := by
        intro j _
        rw [comm_sub_right, comm_smul_right, comm_smul_right,
          rpa.comm_Q_Qdag k j, rpa.comm_Q_Q k j, smul_zero, sub_zero]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hsub, Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [Ne.symm hjk]
      · intro hnk; exact False.elim (hnk hk)
    rw [h_inner_dag, h_inner_q, smul_smul, smul_smul, mul_comm (x i) (A_mat k i),
      mul_comm (y i) (B_mat k i), add_smul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul]

omit [Algebra ℝ A] in
private theorem comm_Qdag_eom_rpaMode (s : Finset ι) (H : A) (A_mat B_mat : ι → ι → R)
    (x y : ι → R) (k : ι) (hk : k ∈ s)
    (h_eom_Qdag : ∀ i ∈ s, comm H (rpa.Qdag i) =
      ∑ j ∈ s, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j))
    (h_eom_Q : ∀ i ∈ s, comm H (rpa.Q i) =
      ∑ j ∈ s, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j)) :
    comm (rpa.Qdag k) (comm H (rpa.rpaMode s x y)) =
      (∑ i ∈ s, (B_mat k i * x i + A_mat k i * y i)) • (1 : A) := by
  dsimp [rpaMode]
  rw [comm_sum_right, comm_sum_right]
  have hQdag_Q (i j : ι) : comm (rpa.Qdag i) (rpa.Q j) = -(if j = i then (1 : A) else 0) := by
    have h := rpa.comm_Q_Qdag j i
    dsimp [comm] at h ⊢
    rw [← h]
    abel
  have hterm : ∀ i ∈ s,
      comm (rpa.Qdag k) (comm H (x i • rpa.Qdag i + y i • rpa.Q i)) =
        (B_mat k i * x i + A_mat k i * y i) • (1 : A) := by
    intro i hi
    rw [comm_add_right, comm_smul_right, comm_smul_right,
      comm_add_right, comm_smul_right, comm_smul_right,
      h_eom_Qdag i hi, h_eom_Q i hi]
    have h_inner_dag : comm (rpa.Qdag k)
        (∑ j ∈ s, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j)) =
        B_mat k i • (1 : A) := by
      rw [comm_sum_right]
      have hsub : ∀ j ∈ s,
          comm (rpa.Qdag k) (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j) =
            (if k = j then B_mat j i else 0) • (1 : A) := by
        intro j _
        rw [comm_sub_right, comm_smul_right, comm_smul_right,
          rpa.comm_Qdag_Qdag k j, hQdag_Q k j, smul_zero, zero_sub]
        by_cases hkj : k = j
        · subst hkj; simp [smul_neg]
        · simp [hkj, Ne.symm hkj]
      rw [Finset.sum_congr rfl hsub, Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [Ne.symm hjk]
      · intro hnk; exact False.elim (hnk hk)
    have h_inner_q : comm (rpa.Qdag k)
        (∑ j ∈ s, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j)) =
        A_mat k i • (1 : A) := by
      rw [comm_sum_right]
      have hsub : ∀ j ∈ s,
          comm (rpa.Qdag k) (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j) =
            (if k = j then A_mat j i else 0) • (1 : A) := by
        intro j _
        rw [comm_sub_right, comm_smul_right, comm_smul_right,
          rpa.comm_Qdag_Qdag k j, hQdag_Q k j, smul_zero, zero_sub]
        by_cases hkj : k = j
        · subst hkj; simp [smul_neg]
        · simp [hkj, Ne.symm hkj]
      rw [Finset.sum_congr rfl hsub, Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [Ne.symm hjk]
      · intro hnk; exact False.elim (hnk hk)
    rw [h_inner_dag, h_inner_q, smul_smul, smul_smul, mul_comm (x i) (B_mat k i),
      mul_comm (y i) (A_mat k i), add_smul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul]

omit [Algebra ℝ A] in
/-- **General Finite RPA Eigenmode Theorem**: under linearized RPA equations of motion on `s`,
if `[H, P(x, y)] = ω • P(x, y)` in a nontrivial algebra over a field `R`, commutator extraction
with `Q_k` and `Q_k†` yields the exact RPA matrix eigenvalue equations
`∑ i ∈ s, (A_{ki} x_i + B_{ki} y_i) = ω x_k` and `∑ i ∈ s, (-B_{ki} x_i - A_{ki} y_i) = ω y_k`. -/
theorem rpa_eigenmode_of_comm {F : Type*} [Field F] [Algebra F A] [Nontrivial A]
    (s : Finset ι) (H : A) (A_mat B_mat : ι → ι → F)
    (x y : ι → F) (ω : F)
    (h_eom_Qdag : ∀ i ∈ s, comm H (rpa.Qdag i) =
      ∑ j ∈ s, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j))
    (h_eom_Q : ∀ i ∈ s, comm H (rpa.Q i) =
      ∑ j ∈ s, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j))
    (h_eig : comm H (rpa.rpaMode s x y) = ω • rpa.rpaMode s x y) :
    ∀ k ∈ s,
      (∑ i ∈ s, (A_mat k i * x i + B_mat k i * y i) = ω * x k) ∧
        (∑ i ∈ s, (-B_mat k i * x i - A_mat k i * y i) = ω * y k) := by
  have smul_one_inj : ∀ c d : F, c • (1 : A) = d • (1 : A) → c = d := by
    intro c d hcd
    by_contra hne
    have hsub : (c - d) • (1 : A) = 0 := by rw [sub_smul, hcd, sub_self]
    have h1 : (1 : A) = 0 := by
      calc (1 : A) = ((c - d)⁻¹ * (c - d)) • (1 : A) := by
            rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
        _ = (c - d)⁻¹ • ((c - d) • (1 : A)) := by rw [smul_smul]
        _ = 0 := by rw [hsub, smul_zero]
    exact one_ne_zero h1
  intro k hk
  have hQ := congrArg (comm (rpa.Q k)) h_eig
  rw [rpa.comm_Q_eom_rpaMode s H A_mat B_mat x y k hk h_eom_Qdag h_eom_Q,
    comm_smul_right, rpa.comm_Q_rpaMode s x y k] at hQ
  simp only [hk, ↓reduceIte, smul_smul] at hQ
  have hQdag := congrArg (comm (rpa.Qdag k)) h_eig
  rw [rpa.comm_Qdag_eom_rpaMode s H A_mat B_mat x y k hk h_eom_Qdag h_eom_Q,
    comm_smul_right, rpa.comm_Qdag_rpaMode s x y k] at hQdag
  simp only [hk, ↓reduceIte, smul_smul] at hQdag
  refine ⟨smul_one_inj _ _ hQ, ?_⟩
  have h2 := smul_one_inj _ _ hQdag
  have hsum : ∑ i ∈ s, (-B_mat k i * x i - A_mat k i * y i) =
      -(∑ i ∈ s, (B_mat k i * x i + A_mat k i * y i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, h2]
  ring

omit [Algebra ℝ A] in
/-- **Thouless / Goldstone Zero-Mode Theorem**: if a symmetry generator `P_0 = P_rest + P(x, y)`
commutes with `H` (`[H, P_0] = 0`) and `P_rest` lies in the commutant of the phonon modes under
`[H, -]`, then `(x, y)` is an exact zero-frequency (`ω = 0`) RPA eigenmode. -/
theorem thouless_goldstone_zero_mode {F : Type*} [Field F] [Algebra F A] [Nontrivial A]
    (s : Finset ι) (H P_rest : A) (A_mat B_mat : ι → ι → F)
    (x y : ι → F)
    (h_eom_Qdag : ∀ i ∈ s, comm H (rpa.Qdag i) =
      ∑ j ∈ s, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j))
    (h_eom_Q : ∀ i ∈ s, comm H (rpa.Q i) =
      ∑ j ∈ s, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j))
    (h_rest : ∀ k ∈ s, comm (rpa.Q k) (comm H P_rest) = 0 ∧ comm (rpa.Qdag k) (comm H P_rest) = 0)
    (h_comm : comm H (P_rest + rpa.rpaMode s x y) = 0) :
    ∀ k ∈ s,
      (∑ i ∈ s, (A_mat k i * x i + B_mat k i * y i) = 0) ∧
        (∑ i ∈ s, (-B_mat k i * x i - A_mat k i * y i) = 0) := by
  have smul_one_zero : ∀ c : F, c • (1 : A) = 0 → c = 0 := by
    intro c hc
    by_contra hne
    have h1 : (1 : A) = 0 := by
      calc (1 : A) = (c⁻¹ * c) • (1 : A) := by rw [inv_mul_cancel₀ hne, one_smul]
        _ = c⁻¹ • (c • (1 : A)) := by rw [smul_smul]
        _ = 0 := by rw [hc, smul_zero]
    exact one_ne_zero h1
  rw [comm_add_right] at h_comm
  intro k hk
  have hQ := congrArg (comm (rpa.Q k)) h_comm
  rw [comm_add_right, (h_rest k hk).1, zero_add,
    rpa.comm_Q_eom_rpaMode s H A_mat B_mat x y k hk h_eom_Qdag h_eom_Q] at hQ
  have hQ_zero : comm (rpa.Q k) (0 : A) = 0 := by dsimp [comm]; simp
  rw [hQ_zero] at hQ
  have hQdag := congrArg (comm (rpa.Qdag k)) h_comm
  rw [comm_add_right, (h_rest k hk).2, zero_add,
    rpa.comm_Qdag_eom_rpaMode s H A_mat B_mat x y k hk h_eom_Qdag h_eom_Q] at hQdag
  have hQdag_zero : comm (rpa.Qdag k) (0 : A) = 0 := by dsimp [comm]; simp
  rw [hQdag_zero] at hQdag
  refine ⟨smul_one_zero _ hQ, ?_⟩
  have h2 := smul_one_zero _ hQdag
  have hsum : ∑ i ∈ s, (-B_mat k i * x i - A_mat k i * y i) =
      -(∑ i ∈ s, (B_mat k i * x i + A_mat k i * y i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, h2, neg_zero]

/-- **Concrete Zero-Frequency Harmonic-Phonon Witness**: a zero-energy mode `omega k = 0`
in `harmonicPhononHamiltonian s omega` yields an explicit conserved generator
`P_0 = Q_k† + Q_k` satisfying `thouless_goldstone_zero_mode`. -/
theorem harmonicPhonon_zero_mode_witness [Nontrivial A]
    (s : Finset ι) (omega : ι → ℝ) (k : ι) (hk : k ∈ s) (hzero : omega k = 0) :
    let H := rpa.harmonicPhononHamiltonian s omega
    let x : ι → ℝ := Pi.single k 1
    let y : ι → ℝ := Pi.single k 1
    let A_mat : ι → ι → ℝ := fun j i => if j = i then omega i else 0
    let B_mat : ι → ι → ℝ := fun _ _ => 0
    comm H (rpa.rpaMode s x y) = 0 ∧
      ∀ m ∈ s,
        (∑ i ∈ s, (A_mat m i * x i + B_mat m i * y i) = 0) ∧
          (∑ i ∈ s, (-B_mat m i * x i - A_mat m i * y i) = 0) := by
  intro H x y A_mat B_mat
  have h_mode : rpa.rpaMode s x y = rpa.Qdag k + rpa.Q k := by
    dsimp [rpaMode]
    rw [Finset.sum_eq_single k]
    · simp [x, y]
    · intro i _ hik
      simp [x, y, hik]
    · intro hnk
      exact False.elim (hnk hk)
  have h_comm : comm H (rpa.rpaMode s x y) = 0 := by
    rw [h_mode, comm_add_right, rpa.comm_harmonicPhononHamiltonian_Qdag s omega k hk,
      rpa.comm_harmonicPhononHamiltonian_Q s omega k hk, hzero]
    simp
  have h_eom_Qdag : ∀ i ∈ s, comm H (rpa.Qdag i) =
      ∑ j ∈ s, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j) := by
    intro i hi
    rw [rpa.comm_harmonicPhononHamiltonian_Qdag s omega i hi, Finset.sum_eq_single i]
    · simp [A_mat, B_mat]
    · intro j _ hji; simp [A_mat, B_mat, hji]
    · intro hni; exact False.elim (hni hi)
  have h_eom_Q : ∀ i ∈ s, comm H (rpa.Q i) =
      ∑ j ∈ s, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j) := by
    intro i hi
    rw [rpa.comm_harmonicPhononHamiltonian_Q s omega i hi, Finset.sum_eq_single i]
    · simp [A_mat, B_mat]
    · intro j _ hji; simp [A_mat, B_mat, hji]
    · intro hni; exact False.elim (hni hi)
  have h_rest : ∀ m ∈ s, comm (rpa.Q m) (comm H (0 : A)) = 0 ∧
      comm (rpa.Qdag m) (comm H (0 : A)) = 0 := by
    intro m _
    constructor <;> simp [comm]
  refine ⟨h_comm, rpa.thouless_goldstone_zero_mode s H 0 A_mat B_mat x y h_eom_Qdag h_eom_Q
    h_rest (by simpa using h_comm)⟩

end ThoulessGoldstone

end PhononRPA

section FockPhononWitness

private def fockQ0 : Module.End ℝ (ℕ × ℕ → ℝ) where
  toFun f p := (p.1 + 1 : ℝ) * f (p.1 + 1, p.2)
  map_add' f g := by ext p; simp [mul_add]
  map_smul' c f := by ext p; simp; ring

private def fockQ1 : Module.End ℝ (ℕ × ℕ → ℝ) where
  toFun f p := (p.2 + 1 : ℝ) * f (p.1, p.2 + 1)
  map_add' f g := by ext p; simp [mul_add]
  map_smul' c f := by ext p; simp; ring

private def fockQdag0 : Module.End ℝ (ℕ × ℕ → ℝ) where
  toFun f p := if p.1 = 0 then 0 else f (p.1 - 1, p.2)
  map_add' f g := by ext p; by_cases h : p.1 = 0 <;> simp [h]
  map_smul' c f := by ext p; by_cases h : p.1 = 0 <;> simp [h]

private def fockQdag1 : Module.End ℝ (ℕ × ℕ → ℝ) where
  toFun f p := if p.2 = 0 then 0 else f (p.1, p.2 - 1)
  map_add' f g := by ext p; by_cases h : p.2 = 0 <;> simp [h]
  map_smul' c f := by ext p; by_cases h : p.2 = 0 <;> simp [h]

/-- Concrete two-mode bosonic Fock shift realization inhabiting `PhononRPA (Fin 2) (Module.End ℝ (ℕ × ℕ → ℝ))`
(`T17` non-vacuity). -/
def fockPhononRPA : PhononRPA (Fin 2) (Module.End ℝ (ℕ × ℕ → ℝ)) where
  Q i := if i = 0 then fockQ0 else fockQ1
  Qdag i := if i = 0 then fockQdag0 else fockQdag1
  comm_Q_Q i j := by
    fin_cases i <;> fin_cases j <;> ext f ⟨m, n⟩ <;> dsimp [comm]
    · simp [fockQ0]
    · change (fockQ0 (fockQ1 f) (m, n)) - (fockQ1 (fockQ0 f) (m, n)) = 0
      simp [fockQ0, fockQ1]; ring
    · change (fockQ1 (fockQ0 f) (m, n)) - (fockQ0 (fockQ1 f) (m, n)) = 0
      simp [fockQ0, fockQ1]; ring
    · simp [fockQ1]
  comm_Qdag_Qdag i j := by
    fin_cases i <;> fin_cases j <;> ext f ⟨m, n⟩ <;> dsimp [comm]
    · simp [fockQdag0]
    · change (fockQdag0 (fockQdag1 f) (m, n)) - (fockQdag1 (fockQdag0 f) (m, n)) = 0
      cases m <;> cases n <;> simp [fockQdag0, fockQdag1]
    · change (fockQdag1 (fockQdag0 f) (m, n)) - (fockQdag0 (fockQdag1 f) (m, n)) = 0
      cases m <;> cases n <;> simp [fockQdag0, fockQdag1]
    · simp [fockQdag1]
  comm_Q_Qdag i j := by
    fin_cases i <;> fin_cases j <;> ext f ⟨m, n⟩ <;> dsimp [comm]
    · change (fockQ0 (fockQdag0 f) (m, n)) - (fockQdag0 (fockQ0 f) (m, n)) = f (m, n)
      cases m with
      | zero => simp [fockQ0, fockQdag0]
      | succ m' =>
        simp only [fockQ0, fockQdag0, LinearMap.coe_mk, AddHom.coe_mk, Nat.succ_ne_zero, ↓reduceIte,
          Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        ring
    · change (fockQ0 (fockQdag1 f) (m, n)) - (fockQdag1 (fockQ0 f) (m, n)) = 0
      cases n with
      | zero => simp [fockQ0, fockQdag1]
      | succ n' => simp [fockQ0, fockQdag1]
    · change (fockQ1 (fockQdag0 f) (m, n)) - (fockQdag0 (fockQ1 f) (m, n)) = 0
      cases m with
      | zero => simp [fockQ1, fockQdag0]
      | succ m' => simp [fockQ1, fockQdag0]
    · change (fockQ1 (fockQdag1 f) (m, n)) - (fockQdag1 (fockQ1 f) (m, n)) = f (m, n)
      cases n with
      | zero => simp [fockQ1, fockQdag1]
      | succ n' =>
        simp only [fockQ1, fockQdag1, LinearMap.coe_mk, AddHom.coe_mk, Nat.succ_ne_zero, ↓reduceIte,
          Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        ring

/-- Non-vacuous `PhononRPA` Thouless zero-mode witness with strictly nonzero ground-state
correlation matrix `B_mat = !![0, -1; -1, 0] ≠ 0`. -/
theorem phononRPA_thouless_witness_B_nonzero :
    let rpa := fockPhononRPA
    let H : Module.End ℝ (ℕ × ℕ → ℝ) :=
      (rpa.Qdag 0 * rpa.Q 0 + rpa.Qdag 1 * rpa.Q 1) +
        (rpa.Qdag 0 * rpa.Qdag 1 + rpa.Q 0 * rpa.Q 1)
    let A_mat : Fin 2 → Fin 2 → ℝ := !![1, 0; 0, 1]
    let B_mat : Fin 2 → Fin 2 → ℝ := !![0, -1; -1, 0]
    let x : Fin 2 → ℝ := ![1, 0]
    let y : Fin 2 → ℝ := ![0, 1]
    B_mat ≠ 0 ∧
      B_mat 0 1 = -1 ∧
      comm H (rpa.rpaMode Finset.univ x y) = 0 ∧
      ∀ k : Fin 2,
        (∑ i : Fin 2, (A_mat k i * x i + B_mat k i * y i) = 0) ∧
          (∑ i : Fin 2, (-B_mat k i * x i - A_mat k i * y i) = 0) := by
  intro rpa H A_mat B_mat x y
  have : Nontrivial (Module.End ℝ (ℕ × ℕ → ℝ)) := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have hval := congrArg (fun T : Module.End ℝ (ℕ × ℕ → ℝ) => T (fun _ => (1 : ℝ)) (0, 0)) h
    simp at hval
  have h_comm_mul_r : ∀ U W Z : Module.End ℝ (ℕ × ℕ → ℝ),
      comm (U * W) Z = U * comm W Z + comm U Z * W := by
    intro U W Z; dsimp [comm]; simp only [mul_sub, sub_mul, mul_assoc]; abel
  have h_comm_add_l : ∀ U W Z : Module.End ℝ (ℕ × ℕ → ℝ),
      comm (U + W) Z = comm U Z + comm W Z := by
    intro U W Z; dsimp [comm]; simp only [add_mul, mul_add]; abel
  have h_comm_neg_sym : ∀ U W : Module.End ℝ (ℕ × ℕ → ℝ), comm U W = -comm W U := by
    intro U W; dsimp [comm]; abel
  have hQdag_Q (i j : Fin 2) :
      comm (rpa.Qdag i) (rpa.Q j) = if i = j then -1 else 0 := by
    rw [h_comm_neg_sym, rpa.comm_Q_Qdag j i]
    fin_cases i <;> fin_cases j <;> simp
  have h_eom_Qdag : ∀ i ∈ (Finset.univ : Finset (Fin 2)), comm H (rpa.Qdag i) =
      ∑ j : Fin 2, (A_mat j i • rpa.Qdag j - B_mat j i • rpa.Q j) := by
    intro i _
    fin_cases i
    · change comm H (rpa.Qdag 0) = ∑ j : Fin 2, (A_mat j 0 • rpa.Qdag j - B_mat j 0 • rpa.Q j)
      dsimp [H, A_mat, B_mat]
      rw [h_comm_add_l, h_comm_add_l, h_comm_add_l,
        h_comm_mul_r, h_comm_mul_r, h_comm_mul_r, h_comm_mul_r]
      simp [rpa.comm_Qdag_Qdag, rpa.comm_Q_Qdag, Fin.sum_univ_two]
      module
    · change comm H (rpa.Qdag 1) = ∑ j : Fin 2, (A_mat j 1 • rpa.Qdag j - B_mat j 1 • rpa.Q j)
      dsimp [H, A_mat, B_mat]
      rw [h_comm_add_l, h_comm_add_l, h_comm_add_l,
        h_comm_mul_r, h_comm_mul_r, h_comm_mul_r, h_comm_mul_r]
      simp [rpa.comm_Qdag_Qdag, rpa.comm_Q_Qdag, Fin.sum_univ_two]
      module
  have h_eom_Q : ∀ i ∈ (Finset.univ : Finset (Fin 2)), comm H (rpa.Q i) =
      ∑ j : Fin 2, (B_mat j i • rpa.Qdag j - A_mat j i • rpa.Q j) := by
    intro i _
    have h_neg1_l : ∀ T : Module.End ℝ (ℕ × ℕ → ℝ),
        (-1 : Module.End ℝ (ℕ × ℕ → ℝ)) * T = -T := fun T => by ext x; simp
    have h_neg1_r : ∀ T : Module.End ℝ (ℕ × ℕ → ℝ),
        T * (-1 : Module.End ℝ (ℕ × ℕ → ℝ)) = -T := fun T => by ext x; simp
    have h_neg1_s : ∀ T : Module.End ℝ (ℕ × ℕ → ℝ), (-1 : ℝ) • T = -T := fun T => by ext x; simp
    fin_cases i
    · change comm H (rpa.Q 0) = ∑ j : Fin 2, (B_mat j 0 • rpa.Qdag j - A_mat j 0 • rpa.Q j)
      dsimp [H, A_mat, B_mat]
      rw [h_comm_add_l, h_comm_add_l, h_comm_add_l,
        h_comm_mul_r, h_comm_mul_r, h_comm_mul_r, h_comm_mul_r]
      simp [rpa.comm_Q_Q, hQdag_Q, Fin.sum_univ_two]
      try rw [h_neg1_l]
      try rw [h_neg1_l]
      try rw [h_neg1_r]
      try rw [h_neg1_s]
      abel
    · change comm H (rpa.Q 1) = ∑ j : Fin 2, (B_mat j 1 • rpa.Qdag j - A_mat j 1 • rpa.Q j)
      dsimp [H, A_mat, B_mat]
      rw [h_comm_add_l, h_comm_add_l, h_comm_add_l,
        h_comm_mul_r, h_comm_mul_r, h_comm_mul_r, h_comm_mul_r]
      simp [rpa.comm_Q_Q, hQdag_Q, Fin.sum_univ_two]
      try rw [h_neg1_l]
      try rw [h_neg1_r]
      try rw [h_neg1_s]
      abel
  have h_mode : rpa.rpaMode Finset.univ x y = rpa.Qdag 0 + rpa.Q 1 := by
    simp [PhononRPA.rpaMode, Fin.sum_univ_two, x, y]
  have h_comm : comm H (rpa.rpaMode Finset.univ x y) = 0 := by
    rw [h_mode]
    have hadd : comm H (rpa.Qdag 0 + rpa.Q 1) = comm H (rpa.Qdag 0) + comm H (rpa.Q 1) := by
      dsimp [comm]; simp only [mul_add, add_mul]; abel
    rw [hadd, h_eom_Qdag 0 (Finset.mem_univ _), h_eom_Q 1 (Finset.mem_univ _)]
    dsimp [A_mat, B_mat]
    simp [Fin.sum_univ_two]
    module
  have h_rest : ∀ m ∈ (Finset.univ : Finset (Fin 2)),
      comm (rpa.Q m) (comm H (0 : Module.End ℝ (ℕ × ℕ → ℝ))) = 0 ∧
        comm (rpa.Qdag m) (comm H (0 : Module.End ℝ (ℕ × ℕ → ℝ))) = 0 := by
    intro m _
    constructor <;> simp [comm]
  have hBne : B_mat ≠ 0 := by
    intro h0
    have h01 := congrFun (congrFun h0 0) 1
    simp [B_mat] at h01
  have hB01 : B_mat 0 1 = -1 := by simp [B_mat]
  refine ⟨hBne, hB01, h_comm, fun k => ?_⟩
  exact rpa.thouless_goldstone_zero_mode Finset.univ H 0 A_mat B_mat x y
    h_eom_Qdag h_eom_Q h_rest (by simpa using h_comm) k (Finset.mem_univ k)

end FockPhononWitness

/-- Combined Quasiparticle-Phonon System satisfying independent cross-commutation. -/
structure CoupledQuasiparticlePhononSystem
    (ι_qp : Type*) [DecidableEq ι_qp]
    (ι_ph : Type*) [DecidableEq ι_ph]
    (A : Type*) [Ring A] [Algebra ℝ A] where
  car : InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR ι_qp A
  rpa : PhononRPA ι_ph A
  cross_comm_a_Q : ∀ i j, comm (car.a i) (rpa.Q j) = 0
  cross_comm_adag_Q : ∀ i j, comm (car.adag i) (rpa.Q j) = 0
  cross_comm_a_Qdag : ∀ i j, comm (car.a i) (rpa.Qdag j) = 0
  cross_comm_adag_Qdag : ∀ i j, comm (car.adag i) (rpa.Qdag j) = 0

/-! ## TDA Pair ↔ PhononRPA Vacuum QBA Bridge & Microscopic CAR Thouless Theorem -/

section TDABridge

open InfoGeometry.Physics.NuclearQuasiparticleCAR

omit [Algebra ℝ A] in
/-- On any Fock vacuum state `v` (`∀ i, car.a i • v = 0`), orthonormal oriented microscopic
TDA pair operators reproduce all `PhononRPA` commutation actions on `v`. -/
theorem tda_vacuum_matches_phononRPA
    {ι_qp ι_ph R A V : Type*} [DecidableEq ι_qp] [DecidableEq ι_ph]
    [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
    (car : QuasiparticleCAR ι_qp A) (rpa : PhononRPA ι_ph A)
    (v : V) (hvac : ∀ i, car.a i • v = 0)
    (pairs : Finset (ι_qp × ι_qp))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (ψ : ι_ph → ι_qp → ι_qp → R)
    (h_ortho : ∀ μ μ', ∑ p ∈ pairs, ψ μ p.1 p.2 * ψ μ' p.1 p.2 = if μ = μ' then (1 : R) else 0) :
    ∀ μ μ',
      comm (car.tdaPairAnnihilation pairs (ψ μ)) (car.tdaPairAnnihilation pairs (ψ μ')) =
        comm (rpa.Q μ) (rpa.Q μ') ∧
      comm (car.tdaPairCreation pairs (ψ μ)) (car.tdaPairCreation pairs (ψ μ')) =
        comm (rpa.Qdag μ) (rpa.Qdag μ') ∧
      comm (car.tdaPairAnnihilation pairs (ψ μ)) (car.tdaPairCreation pairs (ψ μ')) • v =
        comm (rpa.Q μ) (rpa.Qdag μ') • v := by
  intro μ μ'
  refine ⟨?_, ?_, ?_⟩
  · change QuasiparticleCAR.comm _ _ = _
    rw [car.comm_tdaPairAnnihilation_self, rpa.comm_Q_Q]
  · change QuasiparticleCAR.comm _ _ = _
    rw [car.comm_tdaPairCreation_self, rpa.comm_Qdag_Qdag]
  · change QuasiparticleCAR.comm _ _ • v = _
    rw [car.comm_tdaPair_orthonormal_smul_vacuum v hvac pairs h_no_swap ψ μ μ' (h_ortho μ μ'),
      rpa.comm_Q_Qdag μ μ']
    split_ifs <;> simp

omit [Algebra ℝ A] in
/-- Constructive `PhononRPA` realization from microscopic TDA pair operators under the explicit
operator-level vanishing Pauli-blocking defect hypothesis (QBA limit). -/
def tdaPhononRPA_of_zero_pauliDefect
    {ι_qp ι_ph R A : Type*} [DecidableEq ι_qp] [DecidableEq ι_ph]
    [CommRing R] [Ring A] [Algebra R A]
    (car : QuasiparticleCAR ι_qp A)
    (pairs : Finset (ι_qp × ι_qp))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (ψ : ι_ph → ι_qp → ι_qp → R)
    (h_ortho : ∀ μ μ', ∑ p ∈ pairs, ψ μ p.1 p.2 * ψ μ' p.1 p.2 = if μ = μ' then (1 : R) else 0)
    (h_defect : ∀ μ μ', car.tdaPairPauliDefect pairs pairs (ψ μ) (ψ μ') = 0) :
    PhononRPA ι_ph A where
  Q μ := car.tdaPairAnnihilation pairs (ψ μ)
  Qdag μ := car.tdaPairCreation pairs (ψ μ)
  comm_Q_Q μ μ' := car.comm_tdaPairAnnihilation_self pairs pairs (ψ μ) (ψ μ')
  comm_Qdag_Qdag μ μ' := car.comm_tdaPairCreation_self pairs pairs (ψ μ) (ψ μ')
  comm_Q_Qdag μ μ' := by
    change QuasiparticleCAR.comm _ _ = _
    rw [car.comm_tdaPairAnnihilation_tdaPairCreation_orthonormal pairs h_no_swap ψ μ μ'
      (h_ortho μ μ'), h_defect μ μ', sub_zero]
    split_ifs <;> simp

omit [Algebra ℝ A] in
/-- **Algebraic Obstruction for Static Vacuum Equations of Motion**:
If a fermionic pair operator `X† = car.pairCreation a b` (`a ≠ b`) satisfies a *closed*
single-pair RPA equation of motion `[H, X†] = A0 • X† - B0 • X` on an algebra `A` acting
on a nonzero Fock vacuum `v : V` (`∀ p, car.a p • v = 0`), then `B0 = 0` is forced identically
by the Pauli exclusion identity `X† * X† = 0`. Thus non-zero backward amplitudes `B_mat ≠ 0`
in microscopic fermionic RPA require either Rowe's ground-state-correlated state functional `ω`
(cf. `car_vacuum_thouless_zero_mode`) or `PhononRPA` bosonic realizations. -/
theorem car_operator_eom_single_pair_forces_B_zero
    {ι_qp F A V : Type*} [DecidableEq ι_qp]
    [Field F] [CharZero F] [Ring A] [Algebra F A]
    [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower F A V]
    (car : QuasiparticleCAR ι_qp A)
    (v : V) (hv : v ≠ 0) (hvac : ∀ p, car.a p • v = 0)
    (a b : ι_qp) (hab : a ≠ b) (H : A) (A0 B0 : F)
    (h_eom : comm H (car.pairCreation a b) =
      A0 • car.pairCreation a b - B0 • car.pairAnnihilation a b) :
    B0 = 0 := by
  let X := car.pairAnnihilation a b
  let Y := car.pairCreation a b
  have hadag_sq : ∀ q : ι_qp, car.adag q * car.adag q = 0 := fun q => by
    have h := congrArg (fun z : A => (2 : F)⁻¹ • z) (car.anticomm_adag_adag q q)
    rw [← two_smul F, smul_zero, inv_smul_smul₀ (two_ne_zero : (2 : F) ≠ 0)] at h
    exact h
  have hYY : Y * Y = 0 := by
    dsimp [Y, QuasiparticleCAR.pairCreation]
    calc (car.adag a * car.adag b) * (car.adag a * car.adag b)
        = car.adag a * (car.adag b * car.adag a) * car.adag b := by noncomm_ring
      _ = car.adag a * (-(car.adag a * car.adag b)) * car.adag b := by
            rw [car.adag_mul_adag_comm a b]
      _ = -(car.adag a * car.adag a) * (car.adag b * car.adag b) := by noncomm_ring
      _ = 0 := by rw [hadag_sq a, hadag_sq b, neg_zero, zero_mul]
  have hXYv : (X * Y) • v = v := by
    have hcomm : QuasiparticleCAR.comm X Y =
        1 - (car.numberOp a + car.numberOp b) :=
      car.comm_pairAnnihilation_pairCreation_same a b hab
    have hXv : X • v = 0 := by
      dsimp [X, QuasiparticleCAR.pairAnnihilation]
      rw [mul_smul, hvac a, smul_zero]
    have hNa : car.numberOp a • v = 0 := by
      dsimp [QuasiparticleCAR.numberOp]; rw [mul_smul, hvac a, smul_zero]
    have hNb : car.numberOp b • v = 0 := by
      dsimp [QuasiparticleCAR.numberOp]; rw [mul_smul, hvac b, smul_zero]
    calc (X * Y) • v = (X * Y - Y * X) • v + (Y * X) • v := by rw [← add_smul, sub_add_cancel]
      _ = (QuasiparticleCAR.comm X Y) • v + Y • (X • v) := by rw [mul_smul]; rfl
      _ = (1 - (car.numberOp a + car.numberOp b)) • v := by rw [hcomm, hXv, smul_zero, add_zero]
      _ = v := by rw [sub_smul, one_smul, add_smul, hNa, hNb, add_zero, sub_zero]
  have h_id : Y * comm H Y + comm H Y * Y = 0 := by
    dsimp [comm]
    calc Y * (H * Y - Y * H) + (H * Y - Y * H) * Y
        = H * (Y * Y) - (Y * Y) * H := by noncomm_ring
      _ = 0 := by rw [hYY, mul_zero, zero_mul, sub_self]
  have h_mul : X * (Y * (Y * comm H Y + comm H Y * Y)) = 0 := by
    rw [h_id, mul_zero, mul_zero]
  have h_expand : Y * comm H Y + comm H Y * Y = -(B0 • (Y * X + X * Y)) := by
    rw [h_eom]
    change Y * (A0 • Y - B0 • X) + (A0 • Y - B0 • X) * Y = -(B0 • (Y * X + X * Y))
    simp only [mul_sub, sub_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      hYY, smul_zero, zero_sub, smul_add]
    abel
  rw [h_expand, mul_neg, mul_neg] at h_mul
  have h_act := congrArg (fun z : A => z • v) h_mul
  rw [zero_smul, neg_smul, neg_eq_zero] at h_act
  have h_YX_v : (X * (Y * (Y * X))) • v = 0 := by
    have hXv : X • v = 0 := by
      dsimp [X, QuasiparticleCAR.pairAnnihilation]; rw [mul_smul, hvac a, smul_zero]
    rw [mul_smul, mul_smul, mul_smul, hXv, smul_zero, smul_zero, smul_zero]
  have h_XY_v : (X * (Y * (X * Y))) • v = v := by
    calc (X * (Y * (X * Y))) • v
        = ((X * Y) * (X * Y)) • v := by congr 1; noncomm_ring
      _ = (X * Y) • ((X * Y) • v) := by rw [mul_smul]
      _ = v := by rw [hXYv, hXYv]
  rw [Algebra.mul_smul_comm, Algebra.mul_smul_comm, smul_assoc,
    mul_add, mul_add, add_smul, h_YX_v, h_XY_v, zero_add] at h_act
  exact (smul_eq_zero.mp h_act).resolve_right hv

omit [Algebra ℝ A] in
/-- **Two-Pair Algebraic Obstruction for Static Vacuum Equations of Motion**:
Even for two disjoint quasiparticle pairs `p 0, p 1 : ι_qp × ι_qp` (all 4 indices distinct),
if the commutator `[H, X_i†]` closes in the two-pair operator subspace on a nonzero Fock vacuum `v`
with `2 ≠ 0` in `F`, then **all** backward matrix elements `B_mat k i` vanish identically (`∀ k i, B_mat k i = 0`). -/
theorem car_operator_eom_two_pairs_forces_B_zero
    {ι_qp F A V : Type*} [DecidableEq ι_qp]
    [Field F] [CharZero F] [Ring A] [Algebra F A]
    [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower F A V]
    (car : QuasiparticleCAR ι_qp A)
    (v : V) (hv : v ≠ 0) (hvac : ∀ p, car.a p • v = 0)
    (p : Fin 2 → ι_qp × ι_qp)
    (hp0 : (p 0).1 ≠ (p 0).2) (hp1 : (p 1).1 ≠ (p 1).2)
    (hdisj : (p 0).1 ≠ (p 1).1 ∧ (p 0).1 ≠ (p 1).2 ∧
      (p 0).2 ≠ (p 1).1 ∧ (p 0).2 ≠ (p 1).2)
    (H : A) (A_mat B_mat : Fin 2 → Fin 2 → F)
    (h_eom : ∀ i : Fin 2,
      comm H (car.pairCreation (p i).1 (p i).2) =
        ∑ j : Fin 2, (A_mat j i • car.pairCreation (p j).1 (p j).2 -
          B_mat j i • car.pairAnnihilation (p j).1 (p j).2)) :
    ∀ k i : Fin 2, B_mat k i = 0 := by
  let X : Fin 2 → A := fun m => car.pairAnnihilation (p m).1 (p m).2
  let Xdag : Fin 2 → A := fun m => car.pairCreation (p m).1 (p m).2
  have ha_sq : ∀ q : ι_qp, car.a q * car.a q = 0 := fun q => by
    have h := congrArg (fun z : A => (2 : F)⁻¹ • z) (car.anticomm_a_a q q)
    rw [← two_smul F, smul_zero, inv_smul_smul₀ (two_ne_zero : (2 : F) ≠ 0)] at h
    exact h
  have hadag_sq : ∀ q : ι_qp, car.adag q * car.adag q = 0 := fun q => by
    have h := congrArg (fun z : A => (2 : F)⁻¹ • z) (car.anticomm_adag_adag q q)
    rw [← two_smul F, smul_zero, inv_smul_smul₀ (two_ne_zero : (2 : F) ≠ 0)] at h
    exact h
  have hXdag_sq : ∀ m : Fin 2, Xdag m * Xdag m = 0 := by
    intro m
    dsimp [Xdag, QuasiparticleCAR.pairCreation]
    calc (car.adag (p m).1 * car.adag (p m).2) * (car.adag (p m).1 * car.adag (p m).2)
        = car.adag (p m).1 * (car.adag (p m).2 * car.adag (p m).1) * car.adag (p m).2 := by
            noncomm_ring
      _ = car.adag (p m).1 * (-(car.adag (p m).1 * car.adag (p m).2)) * car.adag (p m).2 := by
            rw [car.adag_mul_adag_comm (p m).1 (p m).2]
      _ = -(car.adag (p m).1 * car.adag (p m).1) * (car.adag (p m).2 * car.adag (p m).2) := by
            noncomm_ring
      _ = 0 := by rw [hadag_sq (p m).1, hadag_sq (p m).2, neg_zero, zero_mul]
  have hX_sq : ∀ m : Fin 2, X m * X m = 0 := by
    intro m
    dsimp [X, QuasiparticleCAR.pairAnnihilation]
    calc (car.a (p m).2 * car.a (p m).1) * (car.a (p m).2 * car.a (p m).1)
        = car.a (p m).2 * (car.a (p m).1 * car.a (p m).2) * car.a (p m).1 := by
            noncomm_ring
      _ = car.a (p m).2 * (-(car.a (p m).2 * car.a (p m).1)) * car.a (p m).1 := by
            rw [eq_neg_of_add_eq_zero_left (car.anticomm_a_a (p m).1 (p m).2)]
      _ = -(car.a (p m).2 * car.a (p m).2) * (car.a (p m).1 * car.a (p m).1) := by
            noncomm_ring
      _ = 0 := by rw [ha_sq (p m).2, ha_sq (p m).1, neg_zero, zero_mul]
  have hXdag_comm : Xdag 0 * Xdag 1 = Xdag 1 * Xdag 0 := by
    have hcomm : QuasiparticleCAR.comm (Xdag 0) (Xdag 1) = 0 := by
      dsimp [Xdag, QuasiparticleCAR.pairCreation]
      exact car.comm_pairCreation_pairCreation (p 0).1 (p 0).2 (p 1).1 (p 1).2
    exact sub_eq_zero.mp hcomm
  have hX_comm_Xdag : ∀ {m n : Fin 2}, m ≠ n → X m * Xdag n = Xdag n * X m := by
    intro m n hmn
    have hcomm : QuasiparticleCAR.comm (X m) (Xdag n) = 0 := by
      fin_cases m <;> fin_cases n
      · exact False.elim (hmn rfl)
      · change QuasiparticleCAR.comm (car.pairAnnihilation (p 0).1 (p 0).2)
          (car.pairCreation (p 1).1 (p 1).2) = 0
        rw [car.comm_pairAnnihilation_pairCreation (p 0).1 (p 0).2 (p 1).1 (p 1).2]
        dsimp [QuasiparticleCAR.pairPauliDefect]
        simp [hdisj.1, hdisj.2.1, hdisj.2.2.1, hdisj.2.2.2]
      · change QuasiparticleCAR.comm (car.pairAnnihilation (p 1).1 (p 1).2)
          (car.pairCreation (p 0).1 (p 0).2) = 0
        rw [car.comm_pairAnnihilation_pairCreation (p 1).1 (p 1).2 (p 0).1 (p 0).2]
        dsimp [QuasiparticleCAR.pairPauliDefect]
        simp [hdisj.1.symm, hdisj.2.2.1.symm, hdisj.2.1.symm, hdisj.2.2.2.symm]
      · exact False.elim (hmn rfl)
    exact sub_eq_zero.mp hcomm
  have hXv : ∀ m : Fin 2, X m • v = 0 := fun m => by
    dsimp [X, QuasiparticleCAR.pairAnnihilation]
    rw [mul_smul, hvac (p m).1, smul_zero]
  have hXXv : ∀ m : Fin 2, (X m * Xdag m) • v = v := fun m => by
    have hpm : (p m).1 ≠ (p m).2 := by
      fin_cases m
      · exact hp0
      · exact hp1
    have hcomm : QuasiparticleCAR.comm (X m) (Xdag m) =
        1 - (car.numberOp (p m).1 + car.numberOp (p m).2) :=
      car.comm_pairAnnihilation_pairCreation_same (p m).1 (p m).2 hpm
    have hN1 : car.numberOp (p m).1 • v = 0 := by
      dsimp [QuasiparticleCAR.numberOp]; rw [mul_smul, hvac (p m).1, smul_zero]
    have hN2 : car.numberOp (p m).2 • v = 0 := by
      dsimp [QuasiparticleCAR.numberOp]; rw [mul_smul, hvac (p m).2, smul_zero]
    calc (X m * Xdag m) • v
        = (X m * Xdag m - Xdag m * X m) • v + (Xdag m * X m) • v := by
            rw [← add_smul, sub_add_cancel]
      _ = (QuasiparticleCAR.comm (X m) (Xdag m)) • v + Xdag m • (X m • v) := by
            rw [mul_smul]; rfl
      _ = (1 - (car.numberOp (p m).1 + car.numberOp (p m).2)) • v := by
            rw [hcomm, hXv m, smul_zero, add_zero]
      _ = v := by rw [sub_smul, one_smul, add_smul, hN1, hN2, add_zero, sub_zero]
  have hXdag_comm_mn : ∀ m n : Fin 2, Xdag m * Xdag n = Xdag n * Xdag m := by
    intro m n
    fin_cases m <;> fin_cases n <;> simp [hXdag_comm]
  intro k i
  by_cases hki : k = i
  · subst hki
    let other : Fin 2 := if k = 0 then 1 else 0
    have hne : k ≠ other := by fin_cases k <;> decide
    have h_id : Xdag k * comm H (Xdag k) + comm H (Xdag k) * Xdag k = 0 := by
      dsimp [comm]
      calc Xdag k * (H * Xdag k - Xdag k * H) + (H * Xdag k - Xdag k * H) * Xdag k
          = H * (Xdag k * Xdag k) - (Xdag k * Xdag k) * H := by noncomm_ring
        _ = 0 := by rw [hXdag_sq k, mul_zero, zero_mul, sub_self]
    have h_eom_k : comm H (Xdag k) =
        (A_mat k k • Xdag k + A_mat other k • Xdag other) -
          (B_mat k k • X k + B_mat other k • X other) := by
      rw [h_eom k, Fin.sum_univ_two]
      fin_cases k <;> simp [other] <;> abel
    have h_mul : X k * (Xdag k * (Xdag k * comm H (Xdag k) + comm H (Xdag k) * Xdag k)) = 0 := by
      rw [h_id, mul_zero, mul_zero]
    have h_expand : Xdag k * comm H (Xdag k) + comm H (Xdag k) * Xdag k =
        (2 : F) • (A_mat other k • (Xdag k * Xdag other)) -
          (B_mat k k • (Xdag k * X k + X k * Xdag k) +
            B_mat other k • (Xdag k * X other + X other * Xdag k)) := by
      rw [h_eom_k]
      simp only [mul_sub, sub_mul, mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
        hXdag_sq k, smul_zero, zero_add, hXdag_comm_mn other k, two_smul, smul_add]
      abel
    rw [h_expand] at h_mul
    have h_act := congrArg (fun z : A => z • v) h_mul
    rw [zero_smul] at h_act
    have hkillA : (X k * (Xdag k * (Xdag k * Xdag other))) • v = 0 := by
      have h3 : Xdag k * (Xdag k * Xdag other) = (Xdag k * Xdag k) * Xdag other :=
        (mul_assoc _ _ _).symm
      rw [h3, hXdag_sq k, zero_mul, mul_zero, zero_smul]
    have hkillBk : (X k * (Xdag k * (Xdag k * X k + X k * Xdag k))) • v = v := by
      calc (X k * (Xdag k * (Xdag k * X k + X k * Xdag k))) • v
          = (X k * ((Xdag k * Xdag k) * X k) + (X k * Xdag k) * (X k * Xdag k)) • v := by
              congr 1; noncomm_ring
        _ = ((X k * Xdag k) * (X k * Xdag k)) • v := by rw [hXdag_sq k, zero_mul, mul_zero, zero_add]
        _ = (X k * Xdag k) • ((X k * Xdag k) • v) := by rw [mul_smul]
        _ = v := by rw [hXXv k, hXXv k]
    have hkillBo : (X k * (Xdag k * (Xdag k * X other + X other * Xdag k))) • v = 0 := by
      calc (X k * (Xdag k * (Xdag k * X other + X other * Xdag k))) • v
          = (X k * ((Xdag k * Xdag k) * X other)) • v +
              (X k * Xdag k * (X other * Xdag k)) • v := by
              rw [← add_smul]; congr 1; noncomm_ring
        _ = (X k * Xdag k * (Xdag k * X other)) • v := by
              rw [hXdag_sq k, zero_mul, mul_zero, zero_smul, zero_add, hX_comm_Xdag hne.symm]
        _ = (X k * Xdag k * Xdag k) • (X other • v) := by
              rw [← mul_smul]; congr 1; noncomm_ring
        _ = 0 := by rw [hXv other, smul_zero]
    have hkillA2 :
        (X k * (Xdag k * ((2 : F) • (A_mat other k • (Xdag k * Xdag other))))) • v = 0 := by
      simp only [two_smul, mul_add, add_smul, Algebra.mul_smul_comm, smul_assoc,
        hkillA, smul_zero, add_zero]
    rw [mul_sub, mul_sub, sub_smul, hkillA2, zero_sub, neg_eq_zero,
      mul_add, mul_add, add_smul] at h_act
    simp only [Algebra.mul_smul_comm, smul_assoc] at h_act
    rw [hkillBk, hkillBo, smul_zero, add_zero] at h_act
    exact (smul_eq_zero.mp h_act).resolve_right hv
  · have h_id : (Xdag k * Xdag i) * comm H (Xdag i) * Xdag k +
        Xdag k * comm H (Xdag i) * (Xdag i * Xdag k) = 0 := by
      dsimp [comm]
      calc (Xdag k * Xdag i) * (H * Xdag i - Xdag i * H) * Xdag k +
            Xdag k * (H * Xdag i - Xdag i * H) * (Xdag i * Xdag k)
          = (Xdag k * Xdag i * H * Xdag i * Xdag k - Xdag k * (Xdag i * Xdag i) * H * Xdag k) +
              (Xdag k * H * (Xdag i * Xdag i) * Xdag k - Xdag k * Xdag i * H * Xdag i * Xdag k) := by
              noncomm_ring
        _ = 0 := by rw [hXdag_sq i]; noncomm_ring
    have h_eom_i : comm H (Xdag i) =
        (A_mat i i • Xdag i + A_mat k i • Xdag k) -
          (B_mat i i • X i + B_mat k i • X k) := by
      rw [h_eom i, Fin.sum_univ_two]
      fin_cases k <;> fin_cases i
      · exact False.elim (hki rfl)
      · simp; abel
      · simp; abel
      · exact False.elim (hki rfl)
    have h_Xcomm : X i * X k = X k * X i := by
      have hcomm : QuasiparticleCAR.comm (X i) (X k) = 0 := by
        dsimp [X, QuasiparticleCAR.pairAnnihilation]
        exact car.comm_pairAnnihilation_pairAnnihilation (p i).1 (p i).2 (p k).1 (p k).2
      exact sub_eq_zero.mp hcomm
    have h_mul : (X i * X k) * ((Xdag k * Xdag i) * comm H (Xdag i) * Xdag k +
        Xdag k * comm H (Xdag i) * (Xdag i * Xdag k)) = 0 := by
      rw [h_id, mul_zero]
    have h_expand : (Xdag k * Xdag i) * comm H (Xdag i) * Xdag k +
        Xdag k * comm H (Xdag i) * (Xdag i * Xdag k) =
        -(B_mat i i • ((Xdag k * Xdag i) * X i * Xdag k + Xdag k * X i * (Xdag i * Xdag k)) +
          B_mat k i • ((Xdag k * Xdag i) * X k * Xdag k + Xdag k * X k * (Xdag i * Xdag k))) := by
      rw [h_eom_i]
      have hA1 : (Xdag k * Xdag i) * Xdag i * Xdag k = 0 := by
        calc (Xdag k * Xdag i) * Xdag i * Xdag k = Xdag k * (Xdag i * Xdag i) * Xdag k := by
              noncomm_ring
          _ = 0 := by rw [hXdag_sq i, mul_zero, zero_mul]
      have hA2 : Xdag k * Xdag i * (Xdag i * Xdag k) = 0 := by
        calc Xdag k * Xdag i * (Xdag i * Xdag k) = Xdag k * (Xdag i * Xdag i) * Xdag k := by
              noncomm_ring
          _ = 0 := by rw [hXdag_sq i, mul_zero, zero_mul]
      have hA3 : (Xdag k * Xdag i) * Xdag k * Xdag k = 0 := by
        calc (Xdag k * Xdag i) * Xdag k * Xdag k = Xdag k * Xdag i * (Xdag k * Xdag k) := by
              noncomm_ring
          _ = 0 := by rw [hXdag_sq k, mul_zero]
      have hA4 : Xdag k * Xdag k * (Xdag i * Xdag k) = 0 := by
        rw [hXdag_sq k, zero_mul]
      simp only [mul_sub, sub_mul, mul_add, add_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
        hA1, hA2, hA3, hA4, smul_zero, add_zero, zero_sub, neg_add_rev, smul_add]
      abel
    rw [h_expand, mul_neg] at h_mul
    have h_act := congrArg (fun z : A => z • v) h_mul
    rw [zero_smul, neg_smul] at h_act
    have hkillBii : ((X i * X k) * ((Xdag k * Xdag i) * X i * Xdag k +
        Xdag k * X i * (Xdag i * Xdag k))) • v = 0 := by
      have h1 : (Xdag k * Xdag i) * X i * Xdag k = Xdag i * X i * (Xdag k * Xdag k) := by
        calc (Xdag k * Xdag i) * X i * Xdag k
            = (Xdag i * Xdag k) * X i * Xdag k := by rw [hXdag_comm_mn k i]
          _ = Xdag i * (Xdag k * X i) * Xdag k := by noncomm_ring
          _ = Xdag i * (X i * Xdag k) * Xdag k := by rw [hX_comm_Xdag (Ne.symm hki)]
          _ = Xdag i * X i * (Xdag k * Xdag k) := by noncomm_ring
      have h2 : Xdag k * X i * (Xdag i * Xdag k) = Xdag k * (Xdag k * (X i * Xdag i)) := by
        calc Xdag k * X i * (Xdag i * Xdag k)
            = Xdag k * (X i * Xdag i) * Xdag k := by noncomm_ring
          _ = Xdag k * ((X i * Xdag i) * Xdag k) := by noncomm_ring
          _ = Xdag k * (Xdag k * (X i * Xdag i)) := by
              have hcomm1 : X i * Xdag k = Xdag k * X i := hX_comm_Xdag (Ne.symm hki)
              calc Xdag k * ((X i * Xdag i) * Xdag k)
                  = Xdag k * (X i * (Xdag i * Xdag k)) := by noncomm_ring
                _ = Xdag k * (X i * (Xdag k * Xdag i)) := by rw [hXdag_comm_mn i k]
                _ = Xdag k * ((X i * Xdag k) * Xdag i) := by noncomm_ring
                _ = Xdag k * ((Xdag k * X i) * Xdag i) := by rw [hcomm1]
                _ = Xdag k * (Xdag k * (X i * Xdag i)) := by noncomm_ring
      rw [h1, hXdag_sq k, mul_zero, zero_add, h2, (mul_assoc (Xdag k) (Xdag k) _).symm,
        hXdag_sq k, zero_mul, mul_zero, zero_smul]
    have htermBki : ((X i * X k) * ((Xdag k * Xdag i) * X k * Xdag k +
        Xdag k * X k * (Xdag i * Xdag k))) • v = (2 : F) • v := by
      have hmid : (Xdag i * Xdag k) • v = (Xdag k * Xdag i) • v := by
        rw [hXdag_comm_mn i k]
      have hXdag_i_k : (X i * X k) • ((Xdag i * Xdag k) • v) = v := by
        calc (X i * X k) • ((Xdag i * Xdag k) • v)
            = (X i * (X k * Xdag i) * Xdag k) • v := by
                rw [← mul_smul]; congr 1; noncomm_ring
          _ = (X i * (Xdag i * X k) * Xdag k) • v := by rw [hX_comm_Xdag hki]
          _ = (X i * Xdag i) • ((X k * Xdag k) • v) := by
                rw [← mul_smul]; congr 1; noncomm_ring
          _ = v := by rw [hXXv k, hXXv i]
      have h1 : ((X i * X k) * ((Xdag k * Xdag i) * X k * Xdag k)) • v = v := by
        calc ((X i * X k) * ((Xdag k * Xdag i) * X k * Xdag k)) • v
            = (X i * X k) • ((Xdag k * Xdag i) • ((X k * Xdag k) • v)) := by
                rw [← mul_smul, ← mul_smul]; congr 1; noncomm_ring
          _ = (X i * X k) • ((Xdag i * Xdag k) • v) := by rw [hXXv k, hmid]
          _ = v := hXdag_i_k
      have h2 : ((X i * X k) * (Xdag k * X k * (Xdag i * Xdag k))) • v = v := by
        calc ((X i * X k) * (Xdag k * X k * (Xdag i * Xdag k))) • v
            = (X i * X k) • ((Xdag k * Xdag i) • ((X k * Xdag k) • v)) := by
                rw [← mul_smul, ← mul_smul]
                congr 1
                calc (X i * X k) * (Xdag k * X k * (Xdag i * Xdag k))
                    = (X i * X k) * (Xdag k * (X k * Xdag i) * Xdag k) := by noncomm_ring
                  _ = (X i * X k) * (Xdag k * (Xdag i * X k) * Xdag k) := by
                        rw [hX_comm_Xdag hki]
                  _ = (X i * X k * (Xdag k * Xdag i)) * (X k * Xdag k) := by noncomm_ring
          _ = (X i * X k) • ((Xdag i * Xdag k) • v) := by rw [hXXv k, hmid]
          _ = v := hXdag_i_k
      rw [mul_add, add_smul, h1, h2, ← two_smul F v]
    rw [mul_add, Algebra.mul_smul_comm, Algebra.mul_smul_comm, add_smul, smul_assoc, smul_assoc,
      hkillBii, htermBki, smul_zero, zero_add, smul_smul, ← neg_smul] at h_act
    have hcoeff : -(B_mat k i * 2) = 0 := (smul_eq_zero.mp h_act).resolve_right hv
    have hmul2 : B_mat k i * 2 = 0 := neg_eq_zero.mp hcoeff
    exact (mul_eq_zero.mp hmul2).resolve_right two_ne_zero

omit [Algebra ℝ A] in
/-- **Microscopic Fermionic-CAR Thouless Zero-Mode Theorem (Rowe State-Functional Formulation)**:
Starting directly from `QuasiparticleCAR ι_qp A` with `star (car.a p) = car.adag p` and a
`star`-invariant state functional `ω : A →ₗ[F] F` (without assuming an operator-level bosonic
`PhononRPA` instance or static closed-subspace vacuum equations of motion), any zero-frequency
mode `P_0 = P_rest + ∑ i ∈ s, (x i • X_i† + y i • X_i)` commuting with a self-adjoint `H`
(`star H = H`) and decoupled from `P_rest` solves the exact homogeneous RPA equations for the
Rowe double-commutator matrices
`A_mat k i = ω [X_k, [H, X_i†]]`, `B_mat k i = ω [X_k†, [H, X_i†]]`.
In contrast to operator-level EOM on a static vacuum (cf. `car_operator_eom_single_pair_forces_B_zero`),
ground-state-correlated functionals generically support `B_mat ≠ 0` (cf. `car_vacuum_thouless_witness_B_nonzero`). -/
theorem car_vacuum_thouless_zero_mode
    {ι_qp ι_ph F A : Type*} [DecidableEq ι_qp] [DecidableEq ι_ph]
    [Field F] [StarRing F] [TrivialStar F] [Ring A] [Algebra F A] [StarRing A] [StarModule F A]
    (car : QuasiparticleCAR ι_qp A)
    (h_star_a : ∀ p, star (car.a p) = car.adag p)
    (ω : A →ₗ[F] F)
    (h_ω_star : ∀ z : A, ω (star z) = ω z)
    (pairs : Finset (ι_qp × ι_qp))
    (ψ : ι_ph → ι_qp → ι_qp → F)
    (s : Finset ι_ph) (H P_rest : A)
    (h_star_H : star H = H)
    (x y : ι_ph → F)
    (h_rest : ∀ k ∈ s,
      ω (comm (car.tdaPairAnnihilation pairs (ψ k)) (comm H P_rest)) = 0 ∧
      ω (comm (car.tdaPairCreation pairs (ψ k)) (comm H P_rest)) = 0)
    (h_comm : comm H (P_rest + ∑ i ∈ s, (x i • car.tdaPairCreation pairs (ψ i) +
      y i • car.tdaPairAnnihilation pairs (ψ i))) = 0) :
    let A_mat : ι_ph → ι_ph → F := fun k i =>
      ω (comm (car.tdaPairAnnihilation pairs (ψ k))
        (comm H (car.tdaPairCreation pairs (ψ i))))
    let B_mat : ι_ph → ι_ph → F := fun k i =>
      ω (comm (car.tdaPairCreation pairs (ψ k))
        (comm H (car.tdaPairCreation pairs (ψ i))))
    ∀ k ∈ s,
      (∑ i ∈ s, (A_mat k i * x i + B_mat k i * y i) = 0) ∧
        (∑ i ∈ s, (-B_mat k i * x i - A_mat k i * y i) = 0) := by
  intro A_mat B_mat k hk
  let X : ι_ph → A := fun μ => car.tdaPairAnnihilation pairs (ψ μ)
  let Xdag : ι_ph → A := fun μ => car.tdaPairCreation pairs (ψ μ)
  have h_star_X : ∀ μ, star (X μ) = Xdag μ := fun μ => by
    dsimp [X, Xdag, QuasiparticleCAR.tdaPairAnnihilation, QuasiparticleCAR.tdaPairCreation,
      QuasiparticleCAR.pairAnnihilation, QuasiparticleCAR.pairCreation]
    rw [star_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [star_smul, star_trivial, star_mul, h_star_a p.1, h_star_a p.2]
  have h_star_Xdag : ∀ μ, star (Xdag μ) = X μ := fun μ => by
    rw [← h_star_X μ, star_star]
  have h_star_comm : ∀ U W : A, star (comm U W) = -comm (star U) (star W) := fun U W => by
    dsimp [comm]; rw [star_sub, star_mul, star_mul]; abel
  have h_B_sym : ∀ k i : ι_ph, ω (comm (X k) (comm H (X i))) = B_mat k i := fun k i => by
    have hs : star (comm (X k) (comm H (X i))) = comm (Xdag k) (comm H (Xdag i)) := by
      rw [h_star_comm, h_star_comm, h_star_X k, h_star_X i, h_star_H]
      simp [comm]; noncomm_ring
    rw [← h_ω_star, hs]
  have h_A_sym : ∀ k i : ι_ph, ω (comm (Xdag k) (comm H (X i))) = A_mat k i := fun k i => by
    have hs : star (comm (Xdag k) (comm H (X i))) = comm (X k) (comm H (Xdag i)) := by
      rw [h_star_comm, h_star_comm, h_star_Xdag k, h_star_X i, h_star_H]
      simp [comm]; noncomm_ring
    rw [← h_ω_star, hs]
  have h_comm_sum : ∀ (t : Finset ι_ph) (Z : A) (f : ι_ph → A),
      comm Z (∑ i ∈ t, f i) = ∑ i ∈ t, comm Z (f i) := fun t Z f => by
    dsimp [comm]; rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have h_comm_add : ∀ U W Z : A, comm U (W + Z) = comm U W + comm U Z := fun U W Z => by
    dsimp [comm]; noncomm_ring
  have h_comm_smul : ∀ (r : F) (U W : A), comm U (r • W) = r • comm U W := fun r U W => by
    dsimp [comm]; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  have h_eq1 := congrArg (fun Z : A => ω (comm (X k) Z)) h_comm
  have h_zero1 : ω (comm (X k) (0 : A)) = 0 := by simp [comm]
  rw [h_zero1, h_comm_add, h_comm_sum s H, h_comm_add, h_comm_sum s (X k), map_add,
    (h_rest k hk).1, zero_add, map_sum] at h_eq1
  have h1_term : ∀ i ∈ s,
      ω (comm (X k) (comm H (x i • Xdag i + y i • X i))) =
        A_mat k i * x i + B_mat k i * y i := fun i _ => by
    rw [h_comm_add, h_comm_smul, h_comm_smul, h_comm_add, h_comm_smul, h_comm_smul,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h_B_sym k i, mul_comm (x i),
      mul_comm (y i)]
  rw [Finset.sum_congr rfl h1_term] at h_eq1
  have h_eq2 := congrArg (fun Z : A => ω (comm (Xdag k) Z)) h_comm
  have h_zero2 : ω (comm (Xdag k) (0 : A)) = 0 := by simp [comm]
  rw [h_zero2, h_comm_add, h_comm_sum s H, h_comm_add, h_comm_sum s (Xdag k), map_add,
    (h_rest k hk).2, zero_add, map_sum] at h_eq2
  have h2_term : ∀ i ∈ s,
      ω (comm (Xdag k) (comm H (x i • Xdag i + y i • X i))) =
        B_mat k i * x i + A_mat k i * y i := fun i _ => by
    rw [h_comm_add, h_comm_smul, h_comm_smul, h_comm_add, h_comm_smul, h_comm_smul,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h_A_sym k i, mul_comm (x i),
      mul_comm (y i)]
  rw [Finset.sum_congr rfl h2_term] at h_eq2
  refine ⟨h_eq1, ?_⟩
  have hsum : ∑ i ∈ s, (-B_mat k i * x i - A_mat k i * y i) =
      -(∑ i ∈ s, (B_mat k i * x i + A_mat k i * y i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, h_eq2, neg_zero]

omit [Algebra ℝ A] in
/-- **Rowe State-Functional Reduction on Any Vacuum State**:
If `ω : A →ₗ[F] F` satisfies `ω (z * car.a p) = 0` and `ω (star z) = ω z` with
`star (car.a p) = car.adag p`, then:
1. `ω [X_k†, [H, X_i†]] = - ω (H * (X_i† * X_k†))` (explicitly non-zero whenever `H` contains
   2p-2h ground-state correlations!), and
2. for orthonormal oriented TDA pairs, `ω [X_k, X_i†] = δ_{ki} * ω 1`. -/
theorem rowe_matrices_eq_vacuum_proj_of_ann_zero
    {ι_qp ι_ph F A : Type*} [DecidableEq ι_qp] [DecidableEq ι_ph]
    [Field F] [StarRing F] [TrivialStar F] [Ring A] [Algebra F A] [StarRing A] [StarModule F A]
    (car : QuasiparticleCAR ι_qp A)
    (h_star_a : ∀ p, star (car.a p) = car.adag p)
    (ω : A →ₗ[F] F)
    (h_ω_star : ∀ z : A, ω (star z) = ω z)
    (h_vac_state : ∀ p (z : A), ω (z * car.a p) = 0)
    (pairs : Finset (ι_qp × ι_qp))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (ψ : ι_ph → ι_qp → ι_qp → F)
    (h_ortho : ∀ μ μ', ∑ p ∈ pairs, ψ μ p.1 p.2 * ψ μ' p.1 p.2 = if μ = μ' then (1 : F) else 0)
    (H : A) (k i : ι_ph) :
    ω (comm (car.tdaPairCreation pairs (ψ k)) (comm H (car.tdaPairCreation pairs (ψ i)))) =
      -ω (H * (car.tdaPairCreation pairs (ψ i) * car.tdaPairCreation pairs (ψ k))) ∧
    ω (comm (car.tdaPairAnnihilation pairs (ψ k)) (car.tdaPairCreation pairs (ψ i))) =
      (if k = i then (1 : F) else 0) * ω 1 := by
  have h_vac_adag : ∀ p (z : A), ω (car.adag p * z) = 0 := fun p z => by
    rw [← h_ω_star, star_mul, ← h_star_a p, star_star]
    exact h_vac_state p (star z)
  have h_vac_Xdag : ∀ μ (z : A), ω (car.tdaPairCreation pairs (ψ μ) * z) = 0 := fun μ z => by
    dsimp [QuasiparticleCAR.tdaPairCreation, QuasiparticleCAR.pairCreation]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [Algebra.smul_mul_assoc, map_smul, mul_assoc, h_vac_adag p.1]
    simp
  have h_vac_def : ∀ k' i' : ι_ph, ω (car.tdaPairPauliDefect pairs pairs (ψ k') (ψ i')) = 0 := by
    intro k' i'
    dsimp [QuasiparticleCAR.tdaPairPauliDefect, QuasiparticleCAR.pairPauliDefect]
    rw [map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [map_smul]
    have hz : ω (((if p.1 = q.1 then car.adag q.2 * car.a p.2 else 0) -
          (if p.2 = q.1 then car.adag q.2 * car.a p.1 else 0)) -
          (if p.1 = q.2 then car.adag q.1 * car.a p.2 else 0) +
          (if p.2 = q.2 then car.adag q.1 * car.a p.1 else 0)) = 0 := by
      simp only [map_sub, map_add]
      split_ifs <;> simp only [map_zero, h_vac_adag, sub_zero, add_zero]
    rw [hz, smul_zero]
  constructor
  · have h_expand : comm (car.tdaPairCreation pairs (ψ k))
        (comm H (car.tdaPairCreation pairs (ψ i))) =
        car.tdaPairCreation pairs (ψ k) * (H * car.tdaPairCreation pairs (ψ i)) -
          car.tdaPairCreation pairs (ψ k) * (car.tdaPairCreation pairs (ψ i) * H) -
          H * (car.tdaPairCreation pairs (ψ i) * car.tdaPairCreation pairs (ψ k)) +
          car.tdaPairCreation pairs (ψ i) * (H * car.tdaPairCreation pairs (ψ k)) := by
      dsimp [comm]; noncomm_ring
    rw [h_expand, map_add, map_sub, map_sub, h_vac_Xdag k, h_vac_Xdag k, h_vac_Xdag i]
    simp
  · change ω (QuasiparticleCAR.comm (car.tdaPairAnnihilation pairs (ψ k))
      (car.tdaPairCreation pairs (ψ i))) = _
    rw [car.comm_tdaPairAnnihilation_tdaPairCreation_orthonormal pairs h_no_swap ψ k i (h_ortho k i),
      map_sub, h_vac_def k i, sub_zero]
    split_ifs <;> simp

section Fin4CARWitness

open Matrix

private def jwSign4 (i : Fin 4) (x : Fin 4 → Bool) : ℝ :=
  ∏ j : Fin 4, (if j < i ∧ x j = true then (-1 : ℝ) else 1)

private lemma jwSign4_sq (i : Fin 4) (x : Fin 4 → Bool) : jwSign4 i x * jwSign4 i x = 1 := by
  dsimp [jwSign4]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  split_ifs <;> ring

private lemma jwSign4_update_self (i : Fin 4) (x : Fin 4 → Bool) (b : Bool) :
    jwSign4 i (Function.update x i b) = jwSign4 i x := by
  dsimp [jwSign4]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j < i
  · rw [Function.update_of_ne (ne_of_lt hj)]
  · simp [hj]

private lemma jwSign4_update_of_lt {i k : Fin 4} (hik : i < k) (x : Fin 4 → Bool)
    (hxi : x i = true) :
    jwSign4 k (Function.update x i false) = -jwSign4 k x := by
  dsimp [jwSign4]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ
      (fun j => if j < k ∧ x j = true then (-1 : ℝ) else 1) (Finset.mem_univ i)]
  have hrest :
      ∏ j ∈ Finset.univ.erase i,
          (if j < k ∧ Function.update x i false j = true then (-1 : ℝ) else 1) =
        ∏ j ∈ Finset.univ.erase i, (if j < k ∧ x j = true then (-1 : ℝ) else 1) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest]
  simp [hik, hxi]

private def jwAnn4 (i : Fin 4) : Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ :=
  fun y x => if x i = true ∧ y = Function.update x i false then jwSign4 i x else 0

private lemma jwAnn4_mul_apply (i k : Fin 4) (y x : Fin 4 → Bool) :
    (jwAnn4 i * jwAnn4 k) y x =
      if x k = true ∧ (Function.update x k false) i = true ∧
          y = Function.update (Function.update x k false) i false then
        jwSign4 i (Function.update x k false) * jwSign4 k x
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases hxk : x k = true
  · simp only [hxk, true_and]
    rw [Finset.sum_eq_single (Function.update x k false)]
    · simp only [jwAnn4, hxk, true_and, ↓reduceIte]
      split_ifs with h1 <;> simp_all
    · intro z _ hz
      have hzero : jwAnn4 k z x = 0 := by simp [jwAnn4, hz]
      rw [hzero, mul_zero]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  · simp only [hxk]
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [jwAnn4, hxk]

private lemma jwAnn4_mul_transpose_apply (i k : Fin 4) (y x : Fin 4 → Bool) :
    (jwAnn4 i * (jwAnn4 k)ᵀ) y x =
      if x k = false ∧ (Function.update x k true) i = true ∧
          y = Function.update (Function.update x k true) i false then
        jwSign4 i (Function.update x k true) * jwSign4 k (Function.update x k true)
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases hxk : x k = false
  · simp only [hxk, true_and]
    rw [Finset.sum_eq_single (Function.update x k true)]
    · have hz1 : (Function.update x k true) k = true := Function.update_self k true x
      have hz2 : x = Function.update (Function.update x k true) k false := by
        ext j
        by_cases hj : j = k
        · subst hj; simp [hxk]
        · simp [hj]
      have hzk : (jwAnn4 k)ᵀ (Function.update x k true) x =
          jwSign4 k (Function.update x k true) := by
        rw [Matrix.transpose_apply]
        dsimp [jwAnn4]
        exact ite_eq_left_iff.mpr fun h => False.elim (h ⟨hz1, hz2⟩)
      rw [hzk]
      dsimp [jwAnn4]
      split_ifs <;> ring
    · intro z _ hz
      have hne : ¬(z k = true ∧ x = Function.update z k false) := by
        rintro ⟨hzk, rfl⟩
        apply hz
        ext j
        by_cases hj : j = k
        · subst hj; simp [hzk]
        · simp [hj]
      simp [jwAnn4, hne]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  · simp only [hxk]
    refine Finset.sum_eq_zero fun z _ => ?_
    have hne : ¬(z k = true ∧ x = Function.update z k false) := by
      rintro ⟨_, rfl⟩
      exact hxk (Function.update_self k false z)
    simp [jwAnn4, hne]

private lemma jwAnn4_transpose_mul_apply (k i : Fin 4) (y x : Fin 4 → Bool) :
    ((jwAnn4 k)ᵀ * jwAnn4 i) y x =
      if x i = true ∧ y k = true ∧
          Function.update x i false = Function.update y k false then
        jwSign4 k y * jwSign4 i x
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases hxi : x i = true
  · simp only [hxi, true_and]
    rw [Finset.sum_eq_single (Function.update x i false)]
    · simp only [Matrix.transpose_apply, jwAnn4, hxi, true_and, ↓reduceIte]
      split_ifs with h1 <;> simp_all
    · intro z _ hz
      have hzero : jwAnn4 i z x = 0 := by simp [jwAnn4, hz]
      rw [hzero, mul_zero]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  · simp only [hxi]
    refine Finset.sum_eq_zero fun z _ => ?_
    simp [jwAnn4, hxi]

/-- Concrete 4-mode Jordan–Wigner CAR realization on `M₁₆(ℝ) = Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ`
with `adag i = (a i)ᵀ = star (a i)`. -/
def fin4CAR : QuasiparticleCAR (Fin 4) (Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ) where
  a := jwAnn4
  adag i := (jwAnn4 i)ᵀ
  anticomm_a_a i j := by
    ext y x
    simp only [Matrix.add_apply, Matrix.zero_apply, jwAnn4_mul_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hij_ne : i ≠ j := ne_of_lt hij
      by_cases hxi : x i = true <;> by_cases hxj : x j = true
      · simp only [Function.update_of_ne hij_ne, Function.update_of_ne hij_ne.symm, hxi, hxj,
          true_and, Function.update_comm hij_ne]
        rw [jwSign4_update_of_lt hij x hxi]
        have hsign_i : jwSign4 i (Function.update x j false) = jwSign4 i x := by
          dsimp [jwSign4]
          refine Finset.prod_congr rfl fun m _ => ?_
          by_cases hm : m < i
          · rw [Function.update_of_ne (ne_of_lt (lt_trans hm hij))]
          · simp [hm]
        rw [hsign_i]
        split_ifs <;> ring
      · simp [Function.update_of_ne hij_ne, Function.update_of_ne hij_ne.symm, hxi, hxj]
      · simp [Function.update_of_ne hij_ne, Function.update_of_ne hij_ne.symm, hxi, hxj]
      · simp [Function.update_of_ne hij_ne, Function.update_of_ne hij_ne.symm, hxi, hxj]
    · simp
    · have hji_ne : j ≠ i := ne_of_lt hji
      by_cases hxi : x i = true <;> by_cases hxj : x j = true
      · simp only [Function.update_of_ne hji_ne, Function.update_of_ne hji_ne.symm, hxi, hxj,
          true_and, Function.update_comm hji_ne]
        rw [jwSign4_update_of_lt hji x hxj]
        have hsign_j : jwSign4 j (Function.update x i false) = jwSign4 j x := by
          dsimp [jwSign4]
          refine Finset.prod_congr rfl fun m _ => ?_
          by_cases hm : m < j
          · rw [Function.update_of_ne (ne_of_lt (lt_trans hm hji))]
          · simp [hm]
        rw [hsign_j]
        split_ifs <;> ring
      · simp [Function.update_of_ne hji_ne, Function.update_of_ne hji_ne.symm, hxi, hxj]
      · simp [Function.update_of_ne hji_ne, Function.update_of_ne hji_ne.symm, hxi, hxj]
      · simp [Function.update_of_ne hji_ne, Function.update_of_ne hji_ne.symm, hxi, hxj]
  anticomm_adag_adag i j := by
    have h : (jwAnn4 j * jwAnn4 i + jwAnn4 i * jwAnn4 j)ᵀ = 0 := by
      have hij : jwAnn4 j * jwAnn4 i + jwAnn4 i * jwAnn4 j = 0 := by
        ext y x
        simp only [Matrix.add_apply, Matrix.zero_apply, jwAnn4_mul_apply]
        rcases lt_trichotomy j i with hji | rfl | hij
        · have hne : j ≠ i := ne_of_lt hji
          by_cases hxj : x j = true <;> by_cases hxi : x i = true
          · simp only [Function.update_of_ne hne, Function.update_of_ne hne.symm, hxj, hxi,
              true_and, Function.update_comm hne]
            rw [jwSign4_update_of_lt hji x hxj]
            have hsign_j : jwSign4 j (Function.update x i false) = jwSign4 j x := by
              dsimp [jwSign4]
              refine Finset.prod_congr rfl fun m _ => ?_
              by_cases hm : m < j
              · rw [Function.update_of_ne (ne_of_lt (lt_trans hm hji))]
              · simp [hm]
            rw [hsign_j]
            split_ifs <;> ring
          · simp [Function.update_of_ne hne, Function.update_of_ne hne.symm, hxj, hxi]
          · simp [Function.update_of_ne hne, Function.update_of_ne hne.symm, hxj, hxi]
          · simp [Function.update_of_ne hne, Function.update_of_ne hne.symm, hxj, hxi]
        · simp
        · have hne : i ≠ j := ne_of_lt hij
          by_cases hxj : x j = true <;> by_cases hxi : x i = true
          · simp only [Function.update_of_ne hne, Function.update_of_ne hne.symm, hxj, hxi,
              true_and, Function.update_comm hne]
            rw [jwSign4_update_of_lt hij x hxi]
            have hsign_i : jwSign4 i (Function.update x j false) = jwSign4 i x := by
              dsimp [jwSign4]
              refine Finset.prod_congr rfl fun m _ => ?_
              by_cases hm : m < i
              · rw [Function.update_of_ne (ne_of_lt (lt_trans hm hij))]
              · simp [hm]
            rw [hsign_i]
            split_ifs <;> ring
          · simp [Function.update_of_ne hne, Function.update_of_ne hne.symm, hxj, hxi]
          · simp [Function.update_of_ne hne, Function.update_of_ne hne.symm, hxj, hxi]
          · simp [Function.update_of_ne hne, Function.update_of_ne hne.symm, hxj, hxi]
      rw [hij, Matrix.transpose_zero]
    simpa [Matrix.transpose_add, Matrix.transpose_mul] using h
  anticomm_a_adag i j := by
    ext y x
    simp only [Matrix.add_apply, jwAnn4_mul_transpose_apply, jwAnn4_transpose_mul_apply]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Matrix.one_apply, Function.update_self, true_and]
      by_cases hyx : y = x
      · subst hyx
        cases hyi : y i <;> simp [hyi, jwSign4_update_self, jwSign4_sq]
      · have h1 : ¬(x i = false ∧ y = Function.update x i false) := by
          rintro ⟨hxi, rfl⟩
          apply hyx
          ext m
          by_cases hm : m = i
          · subst hm; simp [hxi]
          · simp [hm]
        have h2 : ¬(x i = true ∧ y i = true ∧
            Function.update x i false = Function.update y i false) := by
          rintro ⟨hxi, hyi, heq⟩
          apply hyx
          ext m
          by_cases hm : m = i
          · subst hm; simp [hxi, hyi]
          · have hm' := congrFun heq m
            simpa [hm] using hm'.symm
        simp [Function.update_idem, h1, h2, hyx]
    · simp only [hij, ↓reduceIte, Matrix.zero_apply]
      have hne_symm : j ≠ i := Ne.symm hij
      have hsign_eq :
          ∀ (hxj : x j = false) (hxi : x i = true)
            (hy : y = Function.update (Function.update x j true) i false),
          jwSign4 i (Function.update x j true) * jwSign4 j (Function.update x j true) +
            jwSign4 j y * jwSign4 i x = 0 := by
        intro hxj hxi hy
        rw [jwSign4_update_self j x true]
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · have hsi : jwSign4 i (Function.update x j true) = jwSign4 i x := by
            dsimp [jwSign4]
            refine Finset.prod_congr rfl fun m _ => ?_
            by_cases hm : m < i
            · rw [Function.update_of_ne (ne_of_lt (lt_trans hm hlt))]
            · simp [hm]
          have hsj : jwSign4 j y = -jwSign4 j x := by
            rw [hy, jwSign4_update_of_lt hlt (Function.update x j true)
              (by rw [Function.update_of_ne hij]; exact hxi), jwSign4_update_self]
          rw [hsi, hsj]; ring
        · have hsi : jwSign4 i (Function.update x j true) = -jwSign4 i x := by
            dsimp [jwSign4]
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
              ← Finset.mul_prod_erase Finset.univ
                (fun m => if m < i ∧ x m = true then (-1 : ℝ) else 1) (Finset.mem_univ j)]
            have hrest :
                ∏ m ∈ Finset.univ.erase j,
                    (if m < i ∧ Function.update x j true m = true then (-1 : ℝ) else 1) =
                  ∏ m ∈ Finset.univ.erase j,
                    (if m < i ∧ x m = true then (-1 : ℝ) else 1) :=
              Finset.prod_congr rfl fun m hm => by
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
            rw [hrest]
            simp [hgt, hxj]
          have hsj : jwSign4 j y = jwSign4 j x := by
            rw [hy]
            dsimp [jwSign4]
            refine Finset.prod_congr rfl fun m _ => ?_
            by_cases hm : m < j
            · have hmi : m ≠ i := ne_of_lt (lt_trans hm hgt)
              have hmj : m ≠ j := ne_of_lt hm
              simp [hmi, hmj]
            · simp [hm]
          rw [hsi, hsj]; ring
      by_cases h1 : x j = false ∧ (Function.update x j true) i = true ∧
          y = Function.update (Function.update x j true) i false
      · rcases h1 with ⟨hxj, hxi', hy⟩
        have hxi : x i = true := by simpa [hij] using hxi'
        have hupd_j : (Function.update (Function.update x j true) i false) j = true := by
          rw [Function.update_of_ne hne_symm, Function.update_self]
        have heq_upd : Function.update x i false = Function.update y j false := by
          ext m
          by_cases hmi : m = i
          · subst hmi; rw [Function.update_self, Function.update_of_ne hij, hy, Function.update_self]
          · by_cases hmj : m = j
            · subst hmj; rw [Function.update_of_ne hne_symm, Function.update_self, hxj]
            · rw [Function.update_of_ne hmi, Function.update_of_ne hmj, hy,
                Function.update_of_ne hmi, Function.update_of_ne hmj]
        simp only [hxj, hxi', hy, hupd_j, and_self, ↓reduceIte, hxi, heq_upd]
        rw [← hy]
        exact hsign_eq hxj hxi hy
      · have h2 : ¬(x i = true ∧ y j = true ∧
            Function.update x i false = Function.update y j false) := by
          rintro ⟨hxi, hyj, heq_upd⟩
          apply h1
          have hxj : x j = false := by
            have := congrFun heq_upd j
            simpa [hne_symm, hxi] using this
          have hxi' : (Function.update x j true) i = true := by simpa [hij] using hxi
          refine ⟨hxj, hxi', ?_⟩
          ext m
          by_cases hmi : m = i
          · rw [hmi]
            have := congrFun heq_upd i
            simpa [hij] using this.symm
          · by_cases hmj : m = j
            · rw [hmj]; simp [hyj, hne_symm]
            · have := congrFun heq_upd m
              simpa [hmi, hmj] using this.symm
        simp [h1, h2]

/-- Concrete 4-mode microscopic CAR Thouless zero-mode witness proving `car_vacuum_thouless_zero_mode`
is genuinely non-vacuous with strictly nonzero ground-state correlation matrix `B_mat 0 1 = -2 ≠ 0`. -/
theorem car_vacuum_thouless_witness_B_nonzero :
    let A16 := Matrix (Fin 4 → Bool) (Fin 4 → Bool) ℝ
    let pairs : Finset (Fin 4 × Fin 4) := {(0, 1), (2, 3)}
    let ψ : Fin 2 → Fin 4 → Fin 4 → ℝ := fun μ a b =>
      if μ = 0 then (if a = 0 ∧ b = 1 then 1 else 0)
      else (if a = 2 ∧ b = 3 then 1 else 0)
    let vacState : A16 →ₗ[ℝ] ℝ :=
      { toFun := fun M => M (fun _ => false) (fun _ => false)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let X0 := fin4CAR.tdaPairAnnihilation pairs (ψ 0)
    let X1 := fin4CAR.tdaPairAnnihilation pairs (ψ 1)
    let X0d := fin4CAR.tdaPairCreation pairs (ψ 0)
    let X1d := fin4CAR.tdaPairCreation pairs (ψ 1)
    let P0 : A16 := X0d + X1d + X0 + X1
    let H : A16 := P0 * P0
    let A_mat : Fin 2 → Fin 2 → ℝ := fun k i =>
      vacState (comm (fin4CAR.tdaPairAnnihilation pairs (ψ k))
        (comm H (fin4CAR.tdaPairCreation pairs (ψ i))))
    let B_mat : Fin 2 → Fin 2 → ℝ := fun k i =>
      vacState (comm (fin4CAR.tdaPairCreation pairs (ψ k))
        (comm H (fin4CAR.tdaPairCreation pairs (ψ i))))
    let x : Fin 2 → ℝ := ![1, 1]
    let y : Fin 2 → ℝ := ![1, 1]
    B_mat 0 1 = -2 ∧
      B_mat ≠ 0 ∧
      ∀ k ∈ (Finset.univ : Finset (Fin 2)),
        (∑ i ∈ Finset.univ, (A_mat k i * x i + B_mat k i * y i) = 0) ∧
          (∑ i ∈ Finset.univ, (-B_mat k i * x i - A_mat k i * y i) = 0) := by
  intro A16 pairs ψ vacState X0 X1 X0d X1d P0 H A_mat B_mat x y
  have h_star_a : ∀ p : Fin 4, star (fin4CAR.a p) = fin4CAR.adag p := fun _ => rfl
  have h_ω_star : ∀ z : A16, vacState (star z) = vacState z := fun _ => rfl
  have h_vac_state : ∀ p (z : A16), vacState (z * fin4CAR.a p) = 0 := by
    intro p z
    change (z * jwAnn4 p) (fun _ => false) (fun _ => false) = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [jwAnn4]
  have h_star_X0 : star X0 = X0d := by
    dsimp [X0, X0d, QuasiparticleCAR.tdaPairAnnihilation, QuasiparticleCAR.tdaPairCreation,
      QuasiparticleCAR.pairAnnihilation, QuasiparticleCAR.pairCreation]
    simp [pairs, ψ]
    rw [h_star_a 0, h_star_a 1]
  have h_star_X1 : star X1 = X1d := by
    dsimp [X1, X1d, QuasiparticleCAR.tdaPairAnnihilation, QuasiparticleCAR.tdaPairCreation,
      QuasiparticleCAR.pairAnnihilation, QuasiparticleCAR.pairCreation]
    simp [pairs, ψ]
    rw [h_star_a 2, h_star_a 3]
  have h_star_X0d : star X0d = X0 := by rw [← h_star_X0, star_star]
  have h_star_X1d : star X1d = X1 := by rw [← h_star_X1, star_star]
  have h_star_H : star H = H := by
    have h_star_P0 : star P0 = P0 := by
      dsimp [P0]
      rw [star_add, star_add, star_add, h_star_X0d, h_star_X1d, h_star_X0, h_star_X1]
      abel
    dsimp [H]
    rw [star_mul, h_star_P0]
  have h_comm : comm H (0 + ∑ i ∈ (Finset.univ : Finset (Fin 2)),
      (x i • fin4CAR.tdaPairCreation pairs (ψ i) +
        y i • fin4CAR.tdaPairAnnihilation pairs (ψ i))) = 0 := by
    have hsum : (0 : A16) + ∑ i ∈ (Finset.univ : Finset (Fin 2)),
        (x i • fin4CAR.tdaPairCreation pairs (ψ i) +
          y i • fin4CAR.tdaPairAnnihilation pairs (ψ i)) = P0 := by
      simp only [zero_add, Fin.sum_univ_two, x, y, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_smul]
      dsimp [P0, X0d, X1d, X0, X1]
      abel
    rw [hsum]
    dsimp [comm, H]
    noncomm_ring
  have h_rest : ∀ k ∈ (Finset.univ : Finset (Fin 2)),
      vacState (comm (fin4CAR.tdaPairAnnihilation pairs (ψ k)) (comm H (0 : A16))) = 0 ∧
      vacState (comm (fin4CAR.tdaPairCreation pairs (ψ k)) (comm H (0 : A16))) = 0 := by
    intro k _; constructor <;> simp [comm]
  have h_rpa := car_vacuum_thouless_zero_mode fin4CAR h_star_a vacState h_ω_star pairs ψ
    Finset.univ H 0 h_star_H x y h_rest h_comm
  have h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs := by decide
  have h_ortho : ∀ μ μ' : Fin 2,
      ∑ p ∈ pairs, ψ μ p.1 p.2 * ψ μ' p.1 p.2 = if μ = μ' then (1 : ℝ) else 0 := by
    intro μ μ'
    fin_cases μ <;> fin_cases μ' <;> simp [pairs, ψ]
  have hB01 : B_mat 0 1 = -2 := by
    have hred := (rowe_matrices_eq_vacuum_proj_of_ann_zero fin4CAR h_star_a vacState h_ω_star
      h_vac_state pairs h_no_swap ψ h_ortho H 0 1).1
    change B_mat 0 1 = -vacState (H * (X1d * X0d)) at hred
    rw [hred]
    have h_vac_adag : ∀ p (z : A16), vacState (fin4CAR.adag p * z) = 0 := fun p z => by
      rw [← h_ω_star, star_mul, ← h_star_a p, star_star]
      exact h_vac_state p (star z)
    have h_vac_Xdag : ∀ μ (z : A16),
        vacState (fin4CAR.tdaPairCreation pairs (ψ μ) * z) = 0 := fun μ z => by
      dsimp [QuasiparticleCAR.tdaPairCreation, QuasiparticleCAR.pairCreation]
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [Algebra.smul_mul_assoc, map_smul, mul_assoc, h_vac_adag p.1]
      simp
    have hX0d_sq : X0d * X0d = 0 := by
      dsimp [X0d, QuasiparticleCAR.tdaPairCreation, QuasiparticleCAR.pairCreation]
      simp [pairs, ψ]
      calc (fin4CAR.adag 0 * fin4CAR.adag 1) * (fin4CAR.adag 0 * fin4CAR.adag 1)
          = fin4CAR.adag 0 * (fin4CAR.adag 1 * fin4CAR.adag 0) * fin4CAR.adag 1 := by noncomm_ring
        _ = fin4CAR.adag 0 * (-(fin4CAR.adag 0 * fin4CAR.adag 1)) * fin4CAR.adag 1 := by
              rw [fin4CAR.adag_mul_adag_comm 0 1]
        _ = -(fin4CAR.adag 0 * fin4CAR.adag 0) * (fin4CAR.adag 1 * fin4CAR.adag 1) := by
              noncomm_ring
        _ = 0 := by rw [fin4CAR.adag_sq 0, fin4CAR.adag_sq 1, neg_zero, zero_mul]
    have hX1d_sq : X1d * X1d = 0 := by
      dsimp [X1d, QuasiparticleCAR.tdaPairCreation, QuasiparticleCAR.pairCreation]
      simp [pairs, ψ]
      calc (fin4CAR.adag 2 * fin4CAR.adag 3) * (fin4CAR.adag 2 * fin4CAR.adag 3)
          = fin4CAR.adag 2 * (fin4CAR.adag 3 * fin4CAR.adag 2) * fin4CAR.adag 3 := by noncomm_ring
        _ = fin4CAR.adag 2 * (-(fin4CAR.adag 2 * fin4CAR.adag 3)) * fin4CAR.adag 3 := by
              rw [fin4CAR.adag_mul_adag_comm 2 3]
        _ = -(fin4CAR.adag 2 * fin4CAR.adag 2) * (fin4CAR.adag 3 * fin4CAR.adag 3) := by
              noncomm_ring
        _ = 0 := by rw [fin4CAR.adag_sq 2, fin4CAR.adag_sq 3, neg_zero, zero_mul]
    have hX0_sq : X0 * X0 = 0 := by
      have h : star (X0d * X0d) = 0 := by rw [hX0d_sq, star_zero]
      rw [star_mul, h_star_X0d] at h
      exact h
    have hX1_sq : X1 * X1 = 0 := by
      have h : star (X1d * X1d) = 0 := by rw [hX1d_sq, star_zero]
      rw [star_mul, h_star_X1d] at h
      exact h
    have hX0_X1d : X0 * X1d = X1d * X0 := by
      dsimp [X0, X1d, QuasiparticleCAR.tdaPairAnnihilation, QuasiparticleCAR.tdaPairCreation,
        QuasiparticleCAR.pairAnnihilation, QuasiparticleCAR.pairCreation]
      simp [pairs, ψ]
      have hcomm := fin4CAR.comm_pairAnnihilation_pairCreation 0 1 2 3
      have hc0 : QuasiparticleCAR.comm (fin4CAR.pairAnnihilation 0 1)
          (fin4CAR.pairCreation 2 3) = 0 := by
        rw [hcomm]
        dsimp [QuasiparticleCAR.pairPauliDefect]
        simp
      exact sub_eq_zero.mp hc0
    have hX0d_X1d : X0d * X1d = X1d * X0d := by
      dsimp [X0d, X1d, QuasiparticleCAR.tdaPairCreation, QuasiparticleCAR.pairCreation]
      simp [pairs, ψ]
      exact sub_eq_zero.mp (fin4CAR.comm_pairCreation_pairCreation 0 1 2 3)
    have hX0_X1 : X0 * X1 = X1 * X0 := by
      have h : star (X1d * X0d) = star (X0d * X1d) := congrArg star hX0d_X1d.symm
      rw [star_mul, star_mul, h_star_X0d, h_star_X1d] at h
      exact h
    have hX0_step : ∀ Z : A16, vacState ((X0 * X0d) * Z) = vacState Z := by
      intro Z
      have hcomm0 : QuasiparticleCAR.comm (fin4CAR.pairAnnihilation 0 1)
          (fin4CAR.pairCreation 0 1) =
          1 - (fin4CAR.numberOp 0 + fin4CAR.numberOp 1) :=
        fin4CAR.comm_pairAnnihilation_pairCreation_same 0 1 (by decide)
      have hX0_eq : X0 = fin4CAR.pairAnnihilation 0 1 := by
        dsimp [X0, QuasiparticleCAR.tdaPairAnnihilation]
        simp [pairs, ψ]
      have hX0d_eq : X0d = fin4CAR.pairCreation 0 1 := by
        dsimp [X0d, QuasiparticleCAR.tdaPairCreation]
        simp [pairs, ψ]
      have hmul : X0 * X0d = 1 - (fin4CAR.numberOp 0 + fin4CAR.numberOp 1) + X0d * X0 := by
        rw [hX0_eq, hX0d_eq, ← hcomm0]; dsimp [QuasiparticleCAR.comm]; abel
      rw [hmul, add_mul, sub_mul, one_mul, add_mul, map_add, map_sub, map_add]
      have hN0 : vacState (fin4CAR.numberOp 0 * Z) = 0 := by
        dsimp [QuasiparticleCAR.numberOp]; rw [mul_assoc, h_vac_adag 0]
      have hN1 : vacState (fin4CAR.numberOp 1 * Z) = 0 := by
        dsimp [QuasiparticleCAR.numberOp]; rw [mul_assoc, h_vac_adag 1]
      have hXd : vacState ((X0d * X0) * Z) = 0 := by
        rw [mul_assoc]; exact h_vac_Xdag 0 (X0 * Z)
      rw [hN0, hN1, hXd]; simp
    have hX1_step : ∀ Z : A16, vacState ((X1 * X1d) * Z) = vacState Z := by
      intro Z
      have hcomm1 : QuasiparticleCAR.comm (fin4CAR.pairAnnihilation 2 3)
          (fin4CAR.pairCreation 2 3) =
          1 - (fin4CAR.numberOp 2 + fin4CAR.numberOp 3) :=
        fin4CAR.comm_pairAnnihilation_pairCreation_same 2 3 (by decide)
      have hX1_eq : X1 = fin4CAR.pairAnnihilation 2 3 := by
        dsimp [X1, QuasiparticleCAR.tdaPairAnnihilation]
        simp [pairs, ψ]
      have hX1d_eq : X1d = fin4CAR.pairCreation 2 3 := by
        dsimp [X1d, QuasiparticleCAR.tdaPairCreation]
        simp [pairs, ψ]
      have hmul : X1 * X1d = 1 - (fin4CAR.numberOp 2 + fin4CAR.numberOp 3) + X1d * X1 := by
        rw [hX1_eq, hX1d_eq, ← hcomm1]; dsimp [QuasiparticleCAR.comm]; abel
      rw [hmul, add_mul, sub_mul, one_mul, add_mul, map_add, map_sub, map_add]
      have hN2 : vacState (fin4CAR.numberOp 2 * Z) = 0 := by
        dsimp [QuasiparticleCAR.numberOp]; rw [mul_assoc, h_vac_adag 2]
      have hN3 : vacState (fin4CAR.numberOp 3 * Z) = 0 := by
        dsimp [QuasiparticleCAR.numberOp]; rw [mul_assoc, h_vac_adag 3]
      have hXd : vacState ((X1d * X1) * Z) = 0 := by
        rw [mul_assoc]; exact h_vac_Xdag 1 (X1 * Z)
      rw [hN2, hN3, hXd]; simp
    have h_vac_1 : vacState (1 : A16) = 1 := by
      change (1 : A16) (fun _ => false) (fun _ => false) = 1
      rw [Matrix.one_apply_eq]
    have hP0_expand : P0 * (X1d * X0d) = (X0 + X1) * (X1d * X0d) := by
      have h0d : X0d * (X1d * X0d) = 0 := by
        calc X0d * (X1d * X0d) = (X0d * X1d) * X0d := (mul_assoc _ _ _).symm
          _ = (X1d * X0d) * X0d := by rw [hX0d_X1d]
          _ = X1d * (X0d * X0d) := mul_assoc _ _ _
          _ = 0 := by rw [hX0d_sq, mul_zero]
      have h1d : X1d * (X1d * X0d) = 0 := by
        rw [← mul_assoc, hX1d_sq, zero_mul]
      dsimp [P0]
      rw [add_mul, add_mul, add_mul, h0d, h1d]
      noncomm_ring
    have hP0P0 : H * (X1d * X0d) = P0 * ((X0 + X1) * (X1d * X0d)) := by
      dsimp [H]; rw [mul_assoc, hP0_expand]
    have h10 : X1 * X0 * (X1d * X0d) = (X1 * X1d) * (X0 * X0d) := by
      calc X1 * X0 * (X1d * X0d)
          = X1 * (X0 * X1d) * X0d := by noncomm_ring
        _ = X1 * (X1d * X0) * X0d := by rw [hX0_X1d]
        _ = (X1 * X1d) * (X0 * X0d) := by noncomm_ring
    have h01 : X0 * X1 * (X1d * X0d) = (X1 * X1d) * (X0 * X0d) := by
      rw [hX0_X1]; exact h10
    have h_vac_10 : vacState ((X1 * X1d) * (X0 * X0d)) = 1 := by
      rw [hX1_step (X0 * X0d), ← mul_one (X0 * X0d), hX0_step 1, h_vac_1]
    have h_quad : (X0 + X1) * ((X0 + X1) * (X1d * X0d)) =
        (X0 * X1 + X1 * X0) * (X1d * X0d) := by
      have h00 : X0 * X0 * (X1d * X0d) = 0 := by rw [hX0_sq, zero_mul]
      have h11 : X1 * X1 * (X1d * X0d) = 0 := by rw [hX1_sq, zero_mul]
      calc (X0 + X1) * ((X0 + X1) * (X1d * X0d))
          = (X0 * X0 * (X1d * X0d) + X1 * X1 * (X1d * X0d)) +
              (X0 * X1 + X1 * X0) * (X1d * X0d) := by noncomm_ring
        _ = (X0 * X1 + X1 * X0) * (X1d * X0d) := by rw [h00, h11, add_zero, zero_add]
    have hH_vac : vacState (H * (X1d * X0d)) = 2 := by
      rw [hP0P0]
      have hP0_split : P0 = (X0d + X1d) + (X0 + X1) := by dsimp [P0]; abel
      rw [hP0_split, add_mul, map_add, add_mul, map_add,
        h_vac_Xdag 0, h_vac_Xdag 1, add_zero, zero_add,
        h_quad, add_mul, map_add, h01, h10, h_vac_10]
      norm_num
    rw [hH_vac]
  exact ⟨hB01, fun h0 => by have h := congrFun (congrFun h0 0) 1; simp [hB01] at h, h_rpa⟩

end Fin4CARWitness

end TDABridge

/-! ## Okubo's Nonassociative Zilon Algebra & Associator-Modified Marumori Product -/

section OkuboZilonMarumori

/-- Okubo's `(n + 1)²`-dimensional Zilon block carrier over an arbitrary finite mode type `ι`
(`PhysRevC.10.2045`, Eqs. 13–15), encoding `c·1 + ∑ u_i a_i + ∑ v_i a_i† + ∑ M_{ij} a_i† a_j`. -/
@[ext]
structure ZilonBlock (ι : Type*) where
  c : ℝ
  u : ι → ℝ
  v : ι → ℝ
  M : Matrix ι ι ℝ

namespace ZilonBlock

variable {ι : Type*}

instance : Zero (ZilonBlock ι) where
  zero := ⟨0, 0, 0, 0⟩

instance : Add (ZilonBlock ι) where
  add x y := ⟨x.c + y.c, x.u + y.u, x.v + y.v, x.M + y.M⟩

instance : Neg (ZilonBlock ι) where
  neg x := ⟨-x.c, -x.u, -x.v, -x.M⟩

instance : Sub (ZilonBlock ι) where
  sub x y := ⟨x.c - y.c, x.u - y.u, x.v - y.v, x.M - y.M⟩

instance : SMul ℝ (ZilonBlock ι) where
  smul r x := ⟨r * x.c, r • x.u, r • x.v, r • x.M⟩

@[simp] lemma zero_c : (0 : ZilonBlock ι).c = 0 := rfl
@[simp] lemma zero_u : (0 : ZilonBlock ι).u = 0 := rfl
@[simp] lemma zero_v : (0 : ZilonBlock ι).v = 0 := rfl
@[simp] lemma zero_M : (0 : ZilonBlock ι).M = 0 := rfl
@[simp] lemma add_c (x y : ZilonBlock ι) : (x + y).c = x.c + y.c := rfl
@[simp] lemma add_u (x y : ZilonBlock ι) : (x + y).u = x.u + y.u := rfl
@[simp] lemma add_v (x y : ZilonBlock ι) : (x + y).v = x.v + y.v := rfl
@[simp] lemma add_M (x y : ZilonBlock ι) : (x + y).M = x.M + y.M := rfl
@[simp] lemma neg_c (x : ZilonBlock ι) : (-x).c = -x.c := rfl
@[simp] lemma neg_u (x : ZilonBlock ι) : (-x).u = -x.u := rfl
@[simp] lemma neg_v (x : ZilonBlock ι) : (-x).v = -x.v := rfl
@[simp] lemma neg_M (x : ZilonBlock ι) : (-x).M = -x.M := rfl
@[simp] lemma sub_c (x y : ZilonBlock ι) : (x - y).c = x.c - y.c := rfl
@[simp] lemma sub_u (x y : ZilonBlock ι) : (x - y).u = x.u - y.u := rfl
@[simp] lemma sub_v (x y : ZilonBlock ι) : (x - y).v = x.v - y.v := rfl
@[simp] lemma sub_M (x y : ZilonBlock ι) : (x - y).M = x.M - y.M := rfl
@[simp] lemma smul_c (r : ℝ) (x : ZilonBlock ι) : (r • x).c = r * x.c := rfl
@[simp] lemma smul_u (r : ℝ) (x : ZilonBlock ι) : (r • x).u = r • x.u := rfl
@[simp] lemma smul_v (r : ℝ) (x : ZilonBlock ι) : (r • x).v = r • x.v := rfl
@[simp] lemma smul_M (r : ℝ) (x : ZilonBlock ι) : (r • x).M = r • x.M := rfl

instance : AddCommGroup (ZilonBlock ι) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  sub_eq_add_neg x y := by ext <;> simp [sub_eq_add_neg]

instance : Module ℝ (ZilonBlock ι) where
  one_smul x := by ext <;> simp
  mul_smul r s x := by ext <;> simp [mul_assoc]
  smul_zero r := by ext <;> simp
  smul_add r x y := by ext <;> simp [mul_add]
  add_smul r s x := by ext <;> simp [add_mul]
  zero_smul x := by ext <;> simp

section Algebra

variable [Fintype ι] [DecidableEq ι]

/-- Identity element `1` of the Zilon algebra. -/
def zilonOne : ZilonBlock ι := ⟨1, 0, 0, 0⟩

/-- Annihilation generator `a_i` in the Zilon algebra. -/
def zilonA (i : ι) : ZilonBlock ι := ⟨0, Pi.single i 1, 0, 0⟩

/-- Creation generator `a_i†` in the Zilon algebra. -/
def zilonAdag (i : ι) : ZilonBlock ι := ⟨0, 0, Pi.single i 1, 0⟩

/-- Vacuum projector `e = 1 - ∑_i a_i† a_i` in the Zilon algebra. -/
def zilonVacuumProj : ZilonBlock ι := ⟨1, 0, 0, -1⟩

/-- Concrete inhabitant witness for `ZilonBlock` (T17 non-vacuity). -/
def zilonConcreteWitness : ZilonBlock (Fin 2) := zilonA 0 + zilonAdag 1

/-- Nonassociative Zilon multiplication (`PhysRevC.10.2045`). -/
def zilonMul (x y : ZilonBlock ι) : ZilonBlock ι where
  c := x.c * y.c + ∑ i, x.u i * y.v i
  u := fun j => x.c * y.u j + x.u j * y.c + ∑ i, x.u i * y.M i j
  v := fun i => x.c * y.v i + x.v i * y.c + ∑ j, x.M i j * y.v j
  M := Matrix.of fun i j =>
    x.c * y.M i j + y.c * x.M i j + (x.M * y.M) i j + x.v i * y.u j - y.v i * x.u j

/-- Nonassociative Zilon associator `(x, y, z) = (x * y) * z - x * (y * z)`. -/
def zilonAssoc (x y z : ZilonBlock ι) : ZilonBlock ι :=
  zilonMul (zilonMul x y) z - zilonMul x (zilonMul y z)

theorem zilonMul_one (x : ZilonBlock ι) : zilonMul x zilonOne = x := by
  ext <;> simp [zilonMul, zilonOne]

theorem one_zilonMul (x : ZilonBlock ι) : zilonMul zilonOne x = x := by
  ext <;> simp [zilonMul, zilonOne]

theorem zilonA_mul_zilonA (i j : ι) : zilonMul (zilonA i) (zilonA j) = 0 := by
  ext <;> simp [zilonMul, zilonA]

theorem zilonAdag_mul_zilonAdag (i j : ι) : zilonMul (zilonAdag i) (zilonAdag j) = 0 := by
  ext <;> simp [zilonMul, zilonAdag]

theorem zilonA_anticomm_zilonAdag (i j : ι) :
    zilonMul (zilonA i) (zilonAdag j) + zilonMul (zilonAdag j) (zilonA i) =
      if i = j then zilonOne else 0 := by
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    ext k l
    · simp [zilonMul, zilonA, zilonAdag, zilonOne, Pi.single_apply]
    · simp [zilonMul, zilonA, zilonAdag, zilonOne]
    · simp [zilonMul, zilonA, zilonAdag, zilonOne]
    · simp [zilonMul, zilonA, zilonAdag, zilonOne, Pi.single_apply]
  · simp only [hij, ↓reduceIte]
    ext k l
    · simp [zilonMul, zilonA, zilonAdag, Pi.single_apply, Ne.symm hij]
    · simp [zilonMul, zilonA, zilonAdag]
    · simp [zilonMul, zilonA, zilonAdag]
    · simp [zilonMul, zilonA, zilonAdag, Pi.single_apply]

theorem zilonVacuumProj_eq :
    (zilonVacuumProj : ZilonBlock ι) = zilonOne - ∑ i : ι, zilonMul (zilonAdag i) (zilonA i) := by
  have hsum_c : (∑ i : ι, zilonMul (zilonAdag i) (zilonA i)).c = 0 := by
    have hfold : ∀ (s : Finset ι), (∑ i ∈ s, zilonMul (zilonAdag i) (zilonA i)).c =
        ∑ i ∈ s, (zilonMul (zilonAdag i) (zilonA i)).c := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => rw [Finset.sum_insert ha, add_c, ih, Finset.sum_insert ha]
    rw [hfold]
    simp [zilonMul, zilonAdag, zilonA]
  have hsum_u : ∀ j, (∑ i : ι, zilonMul (zilonAdag i) (zilonA i)).u j = 0 := by
    intro j
    have hfold : ∀ (s : Finset ι), (∑ i ∈ s, zilonMul (zilonAdag i) (zilonA i)).u j =
        ∑ i ∈ s, (zilonMul (zilonAdag i) (zilonA i)).u j := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => rw [Finset.sum_insert ha, add_u, Pi.add_apply, ih, Finset.sum_insert ha]
    rw [hfold]
    simp [zilonMul, zilonAdag, zilonA]
  have hsum_v : ∀ j, (∑ i : ι, zilonMul (zilonAdag i) (zilonA i)).v j = 0 := by
    intro j
    have hfold : ∀ (s : Finset ι), (∑ i ∈ s, zilonMul (zilonAdag i) (zilonA i)).v j =
        ∑ i ∈ s, (zilonMul (zilonAdag i) (zilonA i)).v j := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => rw [Finset.sum_insert ha, add_v, Pi.add_apply, ih, Finset.sum_insert ha]
    rw [hfold]
    simp [zilonMul, zilonAdag, zilonA]
  have hsum_M : ∀ k l, (∑ i : ι, zilonMul (zilonAdag i) (zilonA i)).M k l = if k = l then 1 else 0 := by
    intro k l
    have hfold : ∀ (s : Finset ι), (∑ i ∈ s, zilonMul (zilonAdag i) (zilonA i)).M k l =
        ∑ i ∈ s, (zilonMul (zilonAdag i) (zilonA i)).M k l := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, add_M, Matrix.add_apply, ih, Finset.sum_insert ha]
    rw [hfold]
    have hterm : ∀ i : ι, (zilonMul (zilonAdag i) (zilonA i)).M k l =
        if i = k ∧ i = l then 1 else 0 := by
      intro i
      simp only [zilonMul, zilonAdag, zilonA, Matrix.of_apply, Pi.single_apply]
      by_cases hik : k = i <;> by_cases hil : l = i
      · subst hik hil; simp
      · simp [hik, hil, Ne.symm hil]
      · simp [hik, hil, Ne.symm hik]
      · simp [hik, hil, Ne.symm hik]
    simp_rw [hterm]
    by_cases hkl : k = l
    · subst hkl
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hik; simp [hik]
      · intro hnk; exact False.elim (hnk (Finset.mem_univ k))
    · simp only [hkl, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with h
      · exact False.elim (hkl (h.1.symm.trans h.2))
      · rfl
  ext k l
  · simp [zilonVacuumProj, zilonOne, hsum_c]
  · simp [zilonVacuumProj, zilonOne, hsum_u]
  · simp [zilonVacuumProj, zilonOne, hsum_v]
  · simp [zilonVacuumProj, zilonOne, hsum_M, Matrix.one_apply]

/-- Explicit nonzero associator witness for any two distinct modes `i ≠ j` in `ZilonBlock ι`,
establishing genuine nonassociativity of `zilonMul`. -/
theorem zilonAssoc_witness {i j : ι} (hij : i ≠ j) :
    zilonAssoc (zilonA i) (zilonAdag j) zilonVacuumProj =
      ⟨0, 0, 0, Matrix.of fun k l => if k = j ∧ l = i then 1 else 0⟩ ∧
      zilonAssoc (zilonA i) (zilonAdag j) zilonVacuumProj ≠ 0 := by
  have h1 : zilonMul (zilonA i) (zilonAdag j) =
      ⟨0, 0, 0, Matrix.of fun k l => if k = j ∧ l = i then -1 else 0⟩ := by
    ext k l
    · simp only [zilonMul, zilonA, zilonAdag, zero_mul, zero_add, Pi.single_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      by_cases hmi : m = i
      · subst hmi; simp [hij]
      · simp [hmi]
    · simp [zilonMul, zilonA, zilonAdag]
    · simp [zilonMul, zilonA, zilonAdag]
    · simp only [zilonMul, zilonA, zilonAdag, Matrix.of_apply, Pi.single_apply]
      by_cases hkj : k = j <;> by_cases hli : l = i
      · subst hkj hli; simp
      · simp [hkj, hli]
      · simp [hkj, hli]
      · simp [hkj, hli]
  have h1e : zilonMul (zilonMul (zilonA i) (zilonAdag j)) zilonVacuumProj = 0 := by
    rw [h1]
    ext k l
    · simp [zilonMul, zilonVacuumProj]
    · simp [zilonMul, zilonVacuumProj]
    · simp [zilonMul, zilonVacuumProj]
    · simp [zilonMul, zilonVacuumProj, Matrix.mul_apply, Matrix.one_apply]
  have he2 : zilonMul (zilonAdag j) zilonVacuumProj = zilonAdag j := by
    ext k l
    · simp [zilonMul, zilonAdag, zilonVacuumProj]
    · simp [zilonMul, zilonAdag, zilonVacuumProj]
    · simp [zilonMul, zilonAdag, zilonVacuumProj]
    · simp [zilonMul, zilonAdag, zilonVacuumProj]
  have hassoc : zilonAssoc (zilonA i) (zilonAdag j) zilonVacuumProj =
      ⟨0, 0, 0, Matrix.of fun k l => if k = j ∧ l = i then 1 else 0⟩ := by
    dsimp [zilonAssoc]
    rw [h1e, he2, h1]
    ext k l
    · simp
    · simp
    · simp
    · simp only [Matrix.of_apply, zero_sub]
      by_cases h : k = j ∧ l = i
      · simp [h]
      · simp [h]
  refine ⟨hassoc, ?_⟩
  rw [hassoc]
  intro hzero
  have hM := congrArg (fun x => x.M j i) hzero
  simp at hM

/-- Okubo's associator-modified Marumori product (`PhysRevC.10.2045`, Eq. 14 with `α = 1 / 2`):
$x \circ y = xy + \frac{1}{2}\big((x, y, e) - (e, x, y)\big)$. -/
def okuboProduct (x y : ZilonBlock ι) : ZilonBlock ι :=
  zilonMul x y + (1 / 2 : ℝ) •
    (zilonAssoc x y zilonVacuumProj - zilonAssoc zilonVacuumProj x y)

/-- Faithful isomorphism from `ZilonBlock ι` to `(n+1)×(n+1)` matrices `Matrix (Option ι) (Option ι) ℝ`,
sending `none` to the vacuum row/column and `some i` to single-fermion mode `i`. -/
def zilonToMatrix (x : ZilonBlock ι) : Matrix (Option ι) (Option ι) ℝ :=
  Matrix.of fun r s =>
    match r, s with
    | none, none => x.c
    | none, some j => x.u j
    | some i, none => x.v i
    | some i, some j => (if i = j then x.c else 0) + x.M i j

omit [Fintype ι] in
theorem zilonToMatrix_injective : Function.Injective (zilonToMatrix (ι := ι)) := by
  intro x y hxy
  ext i j
  · exact congrFun (congrFun hxy none) none
  · exact congrFun (congrFun hxy none) (some i)
  · exact congrFun (congrFun hxy (some i)) none
  · have hc : x.c = y.c := congrFun (congrFun hxy none) none
    have hij := congrFun (congrFun hxy (some i)) (some j)
    simp only [zilonToMatrix, Matrix.of_apply, hc] at hij
    exact add_left_cancel hij

private theorem zilonMul_zilonVacuumProj (x : ZilonBlock ι) :
    zilonMul x zilonVacuumProj =
      ⟨x.c, 0, x.v, Matrix.of fun i j => -(if i = j then x.c else 0)⟩ := by
  ext i j
  · simp [zilonMul, zilonVacuumProj]
  · simp [zilonMul, zilonVacuumProj, Matrix.one_apply]
  · simp [zilonMul, zilonVacuumProj]
  · simp [zilonMul, zilonVacuumProj, Matrix.mul_apply, Matrix.one_apply]

private theorem zilonVacuumProj_zilonMul (y : ZilonBlock ι) :
    zilonMul zilonVacuumProj y =
      ⟨y.c, y.u, 0, Matrix.of fun i j => -(if i = j then y.c else 0)⟩ := by
  ext i j
  · simp [zilonMul, zilonVacuumProj]
  · simp [zilonMul, zilonVacuumProj]
  · simp [zilonMul, zilonVacuumProj, Matrix.one_apply]
  · simp [zilonMul, zilonVacuumProj, Matrix.mul_apply, Matrix.one_apply]

/-- `zilonToMatrix` intertwines Okubo's associator-modified product `okuboProduct` identically
with ordinary associative matrix multiplication on `Matrix (Option ι) (Option ι) ℝ`. -/
theorem zilonToMatrix_okuboProduct (x y : ZilonBlock ι) :
    zilonToMatrix (okuboProduct x y) = zilonToMatrix x * zilonToMatrix y := by
  have h1 : zilonAssoc x y zilonVacuumProj =
      ⟨0, 0, 0, Matrix.of fun i j =>
        -(if i = j then ∑ k, x.u k * y.v k else 0) + y.v i * x.u j⟩ := by
    dsimp [zilonAssoc]
    rw [zilonMul_zilonVacuumProj, zilonMul_zilonVacuumProj]
    ext i j
    · simp [zilonMul]
    · simp [zilonMul, Matrix.mul_apply]
    · simp [zilonMul]
    · simp [zilonMul, Matrix.mul_apply]
      split_ifs <;> ring
  have h2 : zilonAssoc zilonVacuumProj x y =
      ⟨0, 0, 0, Matrix.of fun i j =>
        (if i = j then ∑ k, x.u k * y.v k else 0) - y.v i * x.u j⟩ := by
    dsimp [zilonAssoc]
    rw [zilonVacuumProj_zilonMul, zilonVacuumProj_zilonMul]
    ext i j
    · simp [zilonMul]
    · simp [zilonMul]
    · simp [zilonMul, Matrix.mul_apply]
    · simp [zilonMul, Matrix.mul_apply]
      split_ifs <;> ring
  have h_okubo : okuboProduct x y =
      ⟨x.c * y.c + ∑ k, x.u k * y.v k,
        fun j => x.c * y.u j + x.u j * y.c + ∑ k, x.u k * y.M k j,
        fun i => x.c * y.v i + x.v i * y.c + ∑ k, x.M i k * y.v k,
        Matrix.of fun i j =>
          x.c * y.M i j + y.c * x.M i j + (x.M * y.M) i j +
            x.v i * y.u j - (if i = j then ∑ k, x.u k * y.v k else 0)⟩ := by
    dsimp [okuboProduct]
    rw [h1, h2]
    ext i j
    · simp [zilonMul]
    · simp [zilonMul]
    · simp [zilonMul]
    · simp [zilonMul]
      ring
  ext r s
  rw [h_okubo, Matrix.mul_apply, Fintype.sum_option]
  rcases r with _ | i <;> rcases s with _ | j
  · simp [zilonToMatrix]
  · simp only [zilonToMatrix, Matrix.of_apply]
    have hsum : ∑ k : ι, x.u k * ((if k = j then y.c else 0) + y.M k j) =
        x.u j * y.c + ∑ k : ι, x.u k * y.M k j := by
      simp_rw [mul_add, mul_ite, mul_zero]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    rw [hsum]
    ring
  · simp only [zilonToMatrix, Matrix.of_apply]
    have hsum : ∑ k : ι, ((if i = k then x.c else 0) + x.M i k) * y.v k =
        x.c * y.v i + ∑ k : ι, x.M i k * y.v k := by
      simp_rw [add_mul, ite_mul, zero_mul]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp
    rw [hsum]
    ring
  · simp only [zilonToMatrix, Matrix.of_apply, Matrix.mul_apply]
    have hsum : ∑ k : ι, ((if i = k then x.c else 0) + x.M i k) *
        ((if k = j then y.c else 0) + y.M k j) =
        (if i = j then x.c * y.c else 0) + x.c * y.M i j + y.c * x.M i j +
          ∑ k : ι, x.M i k * y.M k j := by
      simp_rw [add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero]
      simp only [ite_self, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      ring
    rw [hsum]
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij]; ring

/-- **Associativity of Okubo's Marumori Product** (`PhysRevC.10.2045`, Eq. 14 with `α = 1/2`):
proven cleanly via the faithful matrix representation `zilonToMatrix`. -/
theorem okuboProduct_associative (x y z : ZilonBlock ι) :
    okuboProduct (okuboProduct x y) z = okuboProduct x (okuboProduct y z) := by
  apply zilonToMatrix_injective
  simp only [zilonToMatrix_okuboProduct, Matrix.mul_assoc]

/-- Exact Marshalek-boson / Fock-projection relations for `okuboProduct` (`PhysRevC.10.2045`, Eq. 15). -/
theorem okubo_marshalek_relations (i j : ι) :
    okuboProduct (zilonVacuumProj : ZilonBlock ι) zilonVacuumProj = zilonVacuumProj ∧
      okuboProduct (zilonA i) (zilonAdag j) = (if i = j then zilonVacuumProj else 0) ∧
      okuboProduct (zilonA i) zilonVacuumProj = 0 ∧
      okuboProduct zilonVacuumProj (zilonAdag i) = 0 ∧
      okuboProduct zilonVacuumProj (zilonA i) = zilonA i ∧
      okuboProduct (zilonAdag i) zilonVacuumProj = zilonAdag i := by
  have he : ∀ r s : Option ι, zilonToMatrix (zilonVacuumProj : ZilonBlock ι) r s =
      if r = none ∧ s = none then 1 else 0 := by
    rintro (_ | r) (_ | s) <;> simp [zilonToMatrix, zilonVacuumProj, Matrix.one_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply zilonToMatrix_injective
    rw [zilonToMatrix_okuboProduct]
    ext r s
    rw [Matrix.mul_apply, Fintype.sum_option]
    rcases r with _ | r <;> rcases s with _ | s <;> simp [he]
  · apply zilonToMatrix_injective
    rw [zilonToMatrix_okuboProduct]
    ext r s
    rw [Matrix.mul_apply, Fintype.sum_option]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, he]
      rcases r with _ | r <;> rcases s with _ | s <;>
        simp [zilonToMatrix, zilonA, zilonAdag, Pi.single_apply]
    · simp only [hij, ↓reduceIte]
      rcases r with _ | r <;> rcases s with _ | s <;>
        simp [zilonToMatrix, zilonA, zilonAdag, Ne.symm hij, Pi.single_apply]
  · apply zilonToMatrix_injective
    rw [zilonToMatrix_okuboProduct]
    ext r s
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [he]
    rcases r with _ | r <;> rcases s with _ | s <;> simp [zilonToMatrix, zilonA]
  · apply zilonToMatrix_injective
    rw [zilonToMatrix_okuboProduct]
    ext r s
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [he]
    rcases r with _ | r <;> rcases s with _ | s <;> simp [zilonToMatrix, zilonAdag]
  · apply zilonToMatrix_injective
    rw [zilonToMatrix_okuboProduct]
    ext r s
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [he]
    rcases r with _ | r <;> rcases s with _ | s <;> simp [zilonToMatrix, zilonA]
  · apply zilonToMatrix_injective
    rw [zilonToMatrix_okuboProduct]
    ext r s
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [he]
    rcases r with _ | r <;> rcases s with _ | s <;> simp [zilonToMatrix, zilonAdag]

end Algebra

end ZilonBlock

end OkuboZilonMarumori

/-! ## Microscopic CAR Pair Operators, Taniguchi Eqs. (6a–c, 9–10) Defects, Pauli Blocking, & Goldstone Decoupling -/

section MicroscopicCARAndGoldstone

open InfoGeometry.Physics.NuclearQuasiparticleCAR
open Matrix

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Microscopic fermion-bilinear pair annihilation operator `B_{ij} = a_j a_i`. -/
def pairAnn (car : QuasiparticleCAR ι A) (i j : ι) : A :=
  car.a j * car.a i

/-- Microscopic fermion-bilinear pair creation operator `B_{ij}† = a_i† a_j†`. -/
def pairCre (car : QuasiparticleCAR ι A) (i j : ι) : A :=
  car.adag i * car.adag j

/-- Microscopic one-body fermion scattering operator `N_{pq} = a_p† a_q`. -/
def scatterOp (car : QuasiparticleCAR ι A) (p q : ι) : A :=
  car.adag p * car.a q

/-- Collective Tamm–Dancoff phonon annihilation operator `X_μ`. -/
def tdaPhononAnn {R : Type*} [CommRing R] [Algebra R A]
    (car : QuasiparticleCAR ι A) (pairs : Finset (ι × ι)) (ψ : ι → ι → R) : A :=
  car.tdaPairAnnihilation pairs ψ

/-- Collective Tamm–Dancoff phonon creation operator `X_μ†`. -/
def tdaPhononCre {R : Type*} [CommRing R] [Algebra R A]
    (car : QuasiparticleCAR ι A) (pairs : Finset (ι × ι)) (ψ : ι → ι → R) : A :=
  car.tdaPairCreation pairs ψ

omit [Algebra ℝ A] in
/-- **Taniguchi `2203.03780v3` §2.1 Eq. (6a) Microscopic Pair Commutator Defect**:
`[B_{ij}, B_{kl}†] = (δ_{ik}δ_{jl} - δ_{il}δ_{jk}) - (δ_{ik} N_{lj} + δ_{jl} N_{ki} - δ_{il} N_{kj} - δ_{jk} N_{li})`. -/
theorem comm_pairAnn_pairCre_taniguchi_6a
    (car : QuasiparticleCAR ι A) (i j k l : ι) :
    comm (pairAnn car i j) (pairCre car k l) =
      ((if i = k ∧ j = l then (1 : A) else 0) -
        (if i = l ∧ j = k then (1 : A) else 0)) -
        ((if i = k then scatterOp car l j else 0) +
          (if j = l then scatterOp car k i else 0) -
          (if i = l then scatterOp car k j else 0) -
          (if j = k then scatterOp car l i else 0)) := by
  have h := car.comm_pairAnnihilation_pairCreation i j k l
  rw [show comm (pairAnn car i j) (pairCre car k l) =
      QuasiparticleCAR.comm (car.pairAnnihilation i j) (car.pairCreation k l) from rfl, h]
  have hs1 : ((if i = k then (1 : A) else 0) * (if j = l then 1 else 0)) =
      if i = k ∧ j = l then (1 : A) else 0 := by
    split_ifs <;> simp_all
  have hs2 : ((if j = k then (1 : A) else 0) * (if i = l then 1 else 0)) =
      if i = l ∧ j = k then (1 : A) else 0 := by
    split_ifs <;> simp_all
  rw [hs1, hs2]
  dsimp [QuasiparticleCAR.pairPauliDefect, scatterOp]
  abel

omit [Algebra ℝ A] in
/-- **Fermion–Pair Cross-Commutator Defect (Eq. 6b/6c)**:
`[a_k, B_{ij}†] = δ_{ki} a_j† - δ_{kj} a_i†`, showing why `cross_comm_a_Qdag = 0` fails
microscopically. -/
theorem comm_a_pairCre (car : QuasiparticleCAR ι A) (k i j : ι) :
    comm (car.a k) (pairCre car i j) =
      (if k = i then car.adag j else 0) - (if k = j then car.adag i else 0) := by
  dsimp [comm, pairCre]
  have hki : car.a k * car.adag i =
      (if k = i then (1 : A) else 0) - car.adag i * car.a k :=
    eq_sub_of_add_eq (car.anticomm_a_adag k i)
  have hkj : car.a k * car.adag j =
      (if k = j then (1 : A) else 0) - car.adag j * car.a k :=
    eq_sub_of_add_eq (car.anticomm_a_adag k j)
  calc
    car.a k * (car.adag i * car.adag j) - (car.adag i * car.adag j) * car.a k
      = (car.a k * car.adag i) * car.adag j - (car.adag i * car.adag j) * car.a k := by
          simp only [mul_assoc]
    _ = ((if k = i then (1 : A) else 0) - car.adag i * car.a k) * car.adag j -
          (car.adag i * car.adag j) * car.a k := by rw [hki]
    _ = (if k = i then car.adag j else 0) - car.adag i * (car.a k * car.adag j) -
          (car.adag i * car.adag j) * car.a k := by
          split_ifs <;> noncomm_ring
    _ = (if k = i then car.adag j else 0) -
          car.adag i * ((if k = j then (1 : A) else 0) - car.adag j * car.a k) -
          (car.adag i * car.adag j) * car.a k := by rw [hkj]
    _ = (if k = i then car.adag j else 0) - (if k = j then car.adag i else 0) := by
          split_ifs <;> noncomm_ring

omit [Algebra ℝ A] in
/-- Dual fermion–pair cross-commutator: `[B_{ij}, a_k†] = δ_{ki} a_j - δ_{kj} a_i`. -/
theorem comm_pairAnn_adag (car : QuasiparticleCAR ι A) (i j k : ι) :
    comm (pairAnn car i j) (car.adag k) =
      (if k = i then car.a j else 0) - (if k = j then car.a i else 0) := by
  dsimp [comm, pairAnn]
  have hik : car.a i * car.adag k =
      (if i = k then (1 : A) else 0) - car.adag k * car.a i :=
    eq_sub_of_add_eq (car.anticomm_a_adag i k)
  have hjk : car.a j * car.adag k =
      (if j = k then (1 : A) else 0) - car.adag k * car.a j :=
    eq_sub_of_add_eq (car.anticomm_a_adag j k)
  calc
    (car.a j * car.a i) * car.adag k - car.adag k * (car.a j * car.a i)
      = car.a j * (car.a i * car.adag k) - car.adag k * (car.a j * car.a i) := by
          simp only [mul_assoc]
    _ = car.a j * ((if i = k then (1 : A) else 0) - car.adag k * car.a i) -
          car.adag k * (car.a j * car.a i) := by rw [hik]
    _ = (if i = k then car.a j else 0) - (car.a j * car.adag k) * car.a i -
          car.adag k * (car.a j * car.a i) := by
          split_ifs <;> noncomm_ring
    _ = (if i = k then car.a j else 0) -
          ((if j = k then (1 : A) else 0) - car.adag k * car.a j) * car.a i -
          car.adag k * (car.a j * car.a i) := by rw [hjk]
    _ = (if k = i then car.a j else 0) - (if k = j then car.a i else 0) := by
          by_cases h1 : i = k <;> by_cases h2 : j = k <;>
            simp [h1, h2, eq_comm] <;> noncomm_ring

omit [Algebra ℝ A] in
/-- **Scattering–Pair Creation Cross-Commutator (Taniguchi Eq. 6b)**:
`[a_p† a_q, B_{ij}†] = δ_{qi} B_{pj}† - δ_{qj} B_{pi}†`. -/
theorem comm_scatterOp_pairCre (car : QuasiparticleCAR ι A) (p q i j : ι) :
    comm (scatterOp car p q) (pairCre car i j) =
      (if q = i then pairCre car p j else 0) - (if q = j then pairCre car p i else 0) := by
  have had : ∀ r s : ι, car.adag r * car.adag s = -(car.adag s * car.adag r) :=
    fun r s => car.adag_mul_adag_comm s r
  have h_adag_pair : car.adag p * pairCre car i j = pairCre car i j * car.adag p := by
    dsimp [pairCre]
    calc
      car.adag p * (car.adag i * car.adag j)
        = (car.adag p * car.adag i) * car.adag j := (mul_assoc _ _ _).symm
      _ = (-(car.adag i * car.adag p)) * car.adag j := by rw [had p i]
      _ = -(car.adag i * (car.adag p * car.adag j)) := by noncomm_ring
      _ = -(car.adag i * (-(car.adag j * car.adag p))) := by rw [had p j]
      _ = (car.adag i * car.adag j) * car.adag p := by noncomm_ring
  have hq := comm_a_pairCre car q i j
  dsimp [comm, scatterOp] at hq ⊢
  calc
    (car.adag p * car.a q) * pairCre car i j - pairCre car i j * (car.adag p * car.a q)
      = car.adag p * (car.a q * pairCre car i j) -
          (pairCre car i j * car.adag p) * car.a q := by simp only [mul_assoc]
    _ = car.adag p * (car.a q * pairCre car i j) -
          (car.adag p * pairCre car i j) * car.a q := by rw [h_adag_pair]
    _ = car.adag p * (car.a q * pairCre car i j - pairCre car i j * car.a q) := by
          noncomm_ring
    _ = car.adag p * ((if q = i then car.adag j else 0) -
          (if q = j then car.adag i else 0)) := by rw [hq]
    _ = (if q = i then pairCre car p j else 0) - (if q = j then pairCre car p i else 0) := by
          dsimp [pairCre]
          split_ifs <;> noncomm_ring

omit [Algebra ℝ A] in
/-- **Pair Annihilation–Scattering Cross-Commutator (Taniguchi Eq. 6c)**:
`[B_{ij}, a_p† a_q] = δ_{pi} B_{qj} - δ_{pj} B_{qi}`. -/
theorem comm_pairAnn_scatterOp (car : QuasiparticleCAR ι A) (i j p q : ι) :
    comm (pairAnn car i j) (scatterOp car p q) =
      (if p = i then pairAnn car q j else 0) - (if p = j then pairAnn car q i else 0) := by
  have haa : ∀ r s : ι, car.a r * car.a s = -(car.a s * car.a r) :=
    fun r s => eq_neg_of_add_eq_zero_left (car.anticomm_a_a r s)
  have h_pair_a : pairAnn car i j * car.a q = car.a q * pairAnn car i j := by
    dsimp [pairAnn]
    calc
      (car.a j * car.a i) * car.a q
        = car.a j * (car.a i * car.a q) := mul_assoc _ _ _
      _ = car.a j * (-(car.a q * car.a i)) := by rw [haa i q]
      _ = -(car.a j * car.a q) * car.a i := by noncomm_ring
      _ = -(-(car.a q * car.a j)) * car.a i := by rw [haa j q]
      _ = car.a q * (car.a j * car.a i) := by noncomm_ring
  have hp := comm_pairAnn_adag car i j p
  dsimp [comm, scatterOp] at hp ⊢
  calc
    pairAnn car i j * (car.adag p * car.a q) - (car.adag p * car.a q) * pairAnn car i j
      = (pairAnn car i j * car.adag p) * car.a q -
          car.adag p * (car.a q * pairAnn car i j) := by simp only [mul_assoc]
    _ = (pairAnn car i j * car.adag p) * car.a q -
          car.adag p * (pairAnn car i j * car.a q) := by rw [h_pair_a]
    _ = (pairAnn car i j * car.adag p - car.adag p * pairAnn car i j) * car.a q := by
          noncomm_ring
    _ = ((if p = i then car.a j else 0) - (if p = j then car.a i else 0)) * car.a q := by
          rw [hp]
    _ = (if p = i then pairAnn car q j else 0) - (if p = j then pairAnn car q i else 0) := by
          dsimp [pairAnn]
          split_ifs <;> noncomm_ring

omit [Algebra ℝ A] in
/-- **Microscopic Double-Commutator Identity (Taniguchi Eq. 9, pair-level)**:
`[[B_{ij}, B_{kl}†], B_{mn}†]` reduces to an explicit 8-term `pairCre` tensor. -/
theorem double_comm_pairAnn_pairCre (car : QuasiparticleCAR ι A) (i j k l m n : ι) :
    comm (comm (pairAnn car i j) (pairCre car k l)) (pairCre car m n) =
      -(if i = k then (if j = m then pairCre car l n else 0) -
          (if j = n then pairCre car l m else 0) else 0) -
        (if j = l then (if i = m then pairCre car k n else 0) -
          (if i = n then pairCre car k m else 0) else 0) +
        (if i = l then (if j = m then pairCre car k n else 0) -
          (if j = n then pairCre car k m else 0) else 0) +
        (if j = k then (if i = m then pairCre car l n else 0) -
          (if i = n then pairCre car l m else 0) else 0) := by
  rw [comm_pairAnn_pairCre_taniguchi_6a]
  have hcomm_sub : ∀ X Y Z : A, comm (X - Y) Z = comm X Z - comm Y Z := by
    intro X Y Z; dsimp [comm]; noncomm_ring
  have hcomm_add : ∀ X Y Z : A, comm (X + Y) Z = comm X Z + comm Y Z := by
    intro X Y Z; dsimp [comm]; noncomm_ring
  have hcomm_one : ∀ Z : A, comm (1 : A) Z = 0 := by
    intro Z; dsimp [comm]; simp
  have hcomm_zero : ∀ Z : A, comm (0 : A) Z = 0 := by
    intro Z; dsimp [comm]; simp
  have h_scalar : comm ((if i = k ∧ j = l then (1 : A) else 0) -
      (if i = l ∧ j = k then (1 : A) else 0)) (pairCre car m n) = 0 := by
    rw [hcomm_sub]
    split_ifs <;> simp [hcomm_one, hcomm_zero]
  rw [hcomm_sub, h_scalar, zero_sub, hcomm_sub, hcomm_sub, hcomm_add]
  have h1 : comm (if i = k then scatterOp car l j else 0) (pairCre car m n) =
      if i = k then (if j = m then pairCre car l n else 0) -
        (if j = n then pairCre car l m else 0) else 0 := by
    by_cases h : i = k <;> simp [h, comm_scatterOp_pairCre, hcomm_zero]
  have h2 : comm (if j = l then scatterOp car k i else 0) (pairCre car m n) =
      if j = l then (if i = m then pairCre car k n else 0) -
        (if i = n then pairCre car k m else 0) else 0 := by
    by_cases h : j = l <;> simp [h, comm_scatterOp_pairCre, hcomm_zero]
  have h3 : comm (if i = l then scatterOp car k j else 0) (pairCre car m n) =
      if i = l then (if j = m then pairCre car k n else 0) -
        (if j = n then pairCre car k m else 0) else 0 := by
    by_cases h : i = l <;> simp [h, comm_scatterOp_pairCre, hcomm_zero]
  have h4 : comm (if j = k then scatterOp car l i else 0) (pairCre car m n) =
      if j = k then (if i = m then pairCre car l n else 0) -
        (if i = n then pairCre car l m else 0) else 0 := by
    by_cases h : j = k <;> simp [h, comm_scatterOp_pairCre, hcomm_zero]
  rw [h1, h2, h3, h4]
  abel

/-! ### Collective TDA `Γ`- and `Y`-Tensor Identities (Taniguchi Eqs. 6a, 7, 9, 10) -/

section CollectiveTaniguchi

variable [Fintype ι]

/-- Taniguchi Eq. (7) particle-hole contraction tensor
`Γ^{μ₁ μ₂}_{a b} = ∑ c, ψ_{μ₁}(a, c) ψ_{μ₂}(b, c)`. -/
def taniguchiGamma {ι_ph : Type*} (ψ : ι_ph → ι → ι → ℝ)
    (μ₁ μ₂ : ι_ph) (a b : ι) : ℝ :=
  ∑ c : ι, ψ μ₁ a c * ψ μ₂ b c

/-- Taniguchi Eq. (10) double-commutator tensor
`Y(μ₁, μ₂, μ₃, μ₄) = ∑ a b, Γ^{μ₁ μ₂}_{a b} Γ^{μ₃ μ₄}_{a b}`. -/
def taniguchiY {ι_ph : Type*} (ψ : ι_ph → ι → ι → ℝ)
    (μ₁ μ₂ μ₃ μ₄ : ι_ph) : ℝ :=
  ∑ a : ι, ∑ b : ι, taniguchiGamma ψ μ₁ μ₂ a b * taniguchiGamma ψ μ₃ μ₄ a b

/-- Helper: contracting any `G : ι → M` with `G c = 0` over an oriented complete pair set `pairs`
recovers `∑ a : ι, G a`. -/
private lemma sum_pairs_contract_eq {M : Type*} [AddCommGroup M]
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (h_cover : ∀ a b : ι, a ≠ b → (a, b) ∈ pairs ∨ (b, a) ∈ pairs)
    (c : ι) (G : ι → M) (hGc : G c = 0) :
    (∑ p ∈ pairs, ((if p.1 = c then G p.2 else 0) + (if p.2 = c then G p.1 else 0))) =
      ∑ a : ι, G a := by
  have hc_diag : (c, c) ∉ pairs := fun h => h_no_swap (c, c) h h
  have ha_eq : ∀ a : ι,
      G a = ∑ p ∈ pairs, ((if p = (c, a) then G a else 0) + (if p = (a, c) then G a else 0)) := by
    intro a
    by_cases hac : a = c
    · subst hac
      rw [hGc]
      symm
      refine Finset.sum_eq_zero fun p hp => ?_
      have hne : p ≠ (a, a) := fun h => hc_diag (h ▸ hp)
      simp [hne]
    · rcases h_cover c a (Ne.symm hac) with hca_in | hac_in
      · have hnot : (a, c) ∉ pairs := h_no_swap (c, a) hca_in
        symm
        rw [Finset.sum_eq_single (c, a)]
        · have hne : (c, a) ≠ (a, c) := fun h => hac (congrArg Prod.snd h)
          simp [hne]
        · intro p hp hpne
          have hp2 : p ≠ (a, c) := fun h => hnot (h ▸ hp)
          simp [hpne, hp2]
        · intro hm; exact False.elim (hm hca_in)
      · have hnot : (c, a) ∉ pairs := h_no_swap (a, c) hac_in
        symm
        rw [Finset.sum_eq_single (a, c)]
        · have hne : (a, c) ≠ (c, a) := fun h => hac (congrArg Prod.fst h)
          simp [hne]
        · intro p hp hpne
          have hp1 : p ≠ (c, a) := fun h => hnot (h ▸ hp)
          simp [hpne, hp1]
        · intro hm; exact False.elim (hm hac_in)
  calc
    (∑ p ∈ pairs, ((if p.1 = c then G p.2 else 0) + (if p.2 = c then G p.1 else 0)))
      = ∑ p ∈ pairs, ∑ a : ι,
          ((if p = (c, a) then G a else 0) + (if p = (a, c) then G a else 0)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_add_distrib]
          have hs1 : (∑ a : ι, if p = (c, a) then G a else 0) =
              if p.1 = c then G p.2 else 0 := by
            by_cases h1 : p.1 = c
            · simp only [h1, ↓reduceIte]
              rw [Finset.sum_eq_single p.2]
              · have hp_eq : p = (c, p.2) := Prod.ext h1 rfl
                rw [hp_eq]
                simp
              · intro a _ hap
                have hne : p ≠ (c, a) := fun h => hap (congrArg Prod.snd h).symm
                simp [hne]
              · intro hm; exact False.elim (hm (Finset.mem_univ _))
            · simp only [h1, ↓reduceIte]
              refine Finset.sum_eq_zero fun a _ => ?_
              have hne : p ≠ (c, a) := fun h => h1 (congrArg Prod.fst h)
              simp [hne]
          have hs2 : (∑ a : ι, if p = (a, c) then G a else 0) =
              if p.2 = c then G p.1 else 0 := by
            by_cases h2 : p.2 = c
            · simp only [h2, ↓reduceIte]
              rw [Finset.sum_eq_single p.1]
              · have hp_eq : p = (p.1, c) := Prod.ext rfl h2
                rw [hp_eq]
                simp
              · intro a _ hap
                have hne : p ≠ (a, c) := fun h => hap (congrArg Prod.fst h).symm
                simp [hne]
              · intro hm; exact False.elim (hm (Finset.mem_univ _))
            · simp only [h2, ↓reduceIte]
              refine Finset.sum_eq_zero fun a _ => ?_
              have hne : p ≠ (a, c) := fun h => h2 (congrArg Prod.snd h)
              simp [hne]
          rw [hs1, hs2]
    _ = ∑ a : ι, ∑ p ∈ pairs,
          ((if p = (c, a) then G a else 0) + (if p = (a, c) then G a else 0)) :=
          Finset.sum_comm
    _ = ∑ a : ι, G a := by
          refine Finset.sum_congr rfl fun a _ => (ha_eq a).symm

/-- Exact Taniguchi Eq. (7) identification of `tdaPairPauliDefect` with `taniguchiGamma`
over `scatterOp`. -/
theorem tdaPairPauliDefect_eq_taniguchiGamma {ι_ph : Type*}
    (car : QuasiparticleCAR ι A)
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (h_cover : ∀ a b : ι, a ≠ b → (a, b) ∈ pairs ∨ (b, a) ∈ pairs)
    (ψ : ι_ph → ι → ι → ℝ)
    (h_anti : ∀ μ a b, ψ μ b a = -ψ μ a b)
    (μ₁ μ₂ : ι_ph) :
    car.tdaPairPauliDefect pairs pairs (ψ μ₁) (ψ μ₂) =
      ∑ a : ι, ∑ b : ι, taniguchiGamma ψ μ₁ μ₂ a b • scatterOp car b a := by
  have hdiag : ∀ μ c, ψ μ c c = 0 := fun μ c => by
    have h := h_anti μ c c
    linarith
  have hsplit : ∀ p q : ι × ι,
      (ψ μ₁ p.1 p.2 * ψ μ₂ q.1 q.2) • car.pairPauliDefect p.1 p.2 q.1 q.2 =
        ∑ c : ι,
          (((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) *
           ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0))) •
          scatterOp car
            (if q.1 = c then q.2 else q.1)
            (if p.1 = c then p.2 else p.1) := by
    intro p q
    by_cases hp : p.1 = p.2
    · rw [hp]
      simp [QuasiparticleCAR.pairPauliDefect, hdiag]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      by_cases hc : p.2 = c
      · simp [hc, hdiag]
      · simp [hc]
    · by_cases hq : q.1 = q.2
      · rw [hq]
        simp [QuasiparticleCAR.pairPauliDefect, hdiag]
        refine (Finset.sum_eq_zero fun c _ => ?_).symm
        by_cases hc : q.2 = c
        · simp [hc, hdiag]
        · simp [hc]
      · have hterm_c : ∀ c : ι,
            (((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) *
             ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0))) •
            scatterOp car
              (if q.1 = c then q.2 else q.1)
              (if p.1 = c then p.2 else p.1) =
            (if c = p.1 ∧ c = q.1 then (ψ μ₁ p.1 p.2 * ψ μ₂ q.1 q.2) • scatterOp car q.2 p.2 else 0) -
            (if c = p.2 ∧ c = q.1 then (ψ μ₁ p.1 p.2 * ψ μ₂ q.1 q.2) • scatterOp car q.2 p.1 else 0) -
            (if c = p.1 ∧ c = q.2 then (ψ μ₁ p.1 p.2 * ψ μ₂ q.1 q.2) • scatterOp car q.1 p.2 else 0) +
            (if c = p.2 ∧ c = q.2 then (ψ μ₁ p.1 p.2 * ψ μ₂ q.1 q.2) • scatterOp car q.1 p.1 else 0) := by
          intro c
          by_cases hc1 : p.1 = c <;> by_cases hc2 : p.2 = c <;>
            by_cases hc3 : q.1 = c <;> by_cases hc4 : q.2 = c
          · exact False.elim (hp (hc1.trans hc2.symm))
          · exact False.elim (hp (hc1.trans hc2.symm))
          · exact False.elim (hp (hc1.trans hc2.symm))
          · exact False.elim (hp (hc1.trans hc2.symm))
          · exact False.elim (hq (hc3.trans hc4.symm))
          · have h2 : c ≠ p.2 := fun h => hc2 h.symm
            have h4 : c ≠ q.2 := fun h => hc4 h.symm
            simp [hc1, hc2, hc3, hc4, h2, h4]
          · have h2 : c ≠ p.2 := fun h => hc2 h.symm
            have h3 : c ≠ q.1 := fun h => hc3 h.symm
            simp [hc1, hc2, hc3, hc4, h2, h3, neg_smul]
          · have h2 : c ≠ p.2 := fun h => hc2 h.symm
            have h3 : c ≠ q.1 := fun h => hc3 h.symm
            have h4 : c ≠ q.2 := fun h => hc4 h.symm
            simp [hc1, hc2, hc3, hc4, h2, h3, h4]
          · exact False.elim (hq (hc3.trans hc4.symm))
          · have h1 : c ≠ p.1 := fun h => hc1 h.symm
            have h4 : c ≠ q.2 := fun h => hc4 h.symm
            simp [hc1, hc2, hc3, hc4, h1, h4, neg_smul]
          · have h1 : c ≠ p.1 := fun h => hc1 h.symm
            have h3 : c ≠ q.1 := fun h => hc3 h.symm
            simp [hc1, hc2, hc3, hc4, h1, h3]
          · have h1 : c ≠ p.1 := fun h => hc1 h.symm
            have h3 : c ≠ q.1 := fun h => hc3 h.symm
            have h4 : c ≠ q.2 := fun h => hc4 h.symm
            simp [hc1, hc2, hc3, hc4, h1, h3, h4]
          · exact False.elim (hq (hc3.trans hc4.symm))
          · have h1 : c ≠ p.1 := fun h => hc1 h.symm
            have h2 : c ≠ p.2 := fun h => hc2 h.symm
            have h4 : c ≠ q.2 := fun h => hc4 h.symm
            simp [hc1, hc2, hc3, hc4, h1, h2, h4]
          · have h1 : c ≠ p.1 := fun h => hc1 h.symm
            have h2 : c ≠ p.2 := fun h => hc2 h.symm
            have h3 : c ≠ q.1 := fun h => hc3 h.symm
            simp [hc1, hc2, hc3, hc4, h1, h2, h3]
          · have h1 : c ≠ p.1 := fun h => hc1 h.symm
            have h2 : c ≠ p.2 := fun h => hc2 h.symm
            have h3 : c ≠ q.1 := fun h => hc3 h.symm
            have h4 : c ≠ q.2 := fun h => hc4 h.symm
            simp [hc1, hc2, hc3, hc4, h1, h2, h3, h4]
        simp_rw [hterm_c, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have hsum_ind : ∀ u v : ι, ∀ (M : A),
            (∑ c : ι, if c = u ∧ c = v then M else 0) = if u = v then M else 0 := by
          intro u v M
          by_cases huv : u = v
          · simp only [huv, ↓reduceIte]
            rw [Finset.sum_eq_single u]
            · simp [huv]
            · intro c _ hcu; rw [← huv]; simp [hcu]
            · intro hm; exact False.elim (hm (Finset.mem_univ _))
          · simp only [huv, ↓reduceIte]
            refine Finset.sum_eq_zero fun c _ => ?_
            split_ifs with h
            · exact False.elim (huv (h.1.symm.trans h.2))
            · rfl
        rw [hsum_ind p.1 q.1, hsum_ind p.2 q.1, hsum_ind p.1 q.2, hsum_ind p.2 q.2]
        dsimp [QuasiparticleCAR.pairPauliDefect, scatterOp]
        simp only [smul_add, smul_sub]
        split_ifs <;> simp only [smul_zero, sub_zero, zero_sub, add_zero]
  dsimp [QuasiparticleCAR.tdaPairPauliDefect]
  simp_rw [hsplit]
  have hsum_c : ∀ c : ι,
      (∑ q ∈ pairs, ∑ p ∈ pairs,
        (((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) *
         ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0))) •
        scatterOp car (if q.1 = c then q.2 else q.1) (if p.1 = c then p.2 else p.1)) =
      ∑ a : ι, ∑ b : ι, (ψ μ₁ a c * ψ μ₂ b c) • scatterOp car b a := by
    intro c
    have h_inner_p : ∀ b : ι,
        (∑ p ∈ pairs,
          ((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) •
            scatterOp car b (if p.1 = c then p.2 else p.1)) =
        -(∑ a : ι, ψ μ₁ a c • scatterOp car b a) := by
      intro b
      have hG : ∀ p ∈ pairs,
          ((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) •
            scatterOp car b (if p.1 = c then p.2 else p.1) =
          -((if p.1 = c then ψ μ₁ p.2 c • scatterOp car b p.2 else 0) +
            (if p.2 = c then ψ μ₁ p.1 c • scatterOp car b p.1 else 0)) := by
        intro p hp
        by_cases h1 : p.1 = c <;> by_cases h2 : p.2 = c
        · have hpp : p.1 = p.2 := h1.trans h2.symm
          exfalso; apply h_no_swap p hp
          have : (p.2, p.1) = p := Prod.ext hpp.symm hpp
          simpa [this] using hp
        · simp [h1, h2, h_anti μ₁ c p.2]
        · simp [h1, h2]
        · simp [h1, h2]
      rw [Finset.sum_congr rfl hG, Finset.sum_neg_distrib]
      congr 1
      exact sum_pairs_contract_eq pairs h_no_swap h_cover c
        (fun a => ψ μ₁ a c • scatterOp car b a) (by simp [hdiag])
    have hfactor : ∀ q ∈ pairs,
        (∑ p ∈ pairs,
          (((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) *
           ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0))) •
          scatterOp car (if q.1 = c then q.2 else q.1) (if p.1 = c then p.2 else p.1)) =
        -((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0)) •
          ∑ a : ι, ψ μ₁ a c • scatterOp car (if q.1 = c then q.2 else q.1) a := by
      intro q _
      simp_rw [mul_comm _ ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0)),
        ← smul_smul, ← Finset.smul_sum, h_inner_p (if q.1 = c then q.2 else q.1),
        smul_neg, neg_smul]
    rw [Finset.sum_congr rfl hfactor]
    have h_outer_q :
        (∑ q ∈ pairs,
          -((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0)) •
            ∑ a : ι, ψ μ₁ a c • scatterOp car (if q.1 = c then q.2 else q.1) a) =
        ∑ b : ι, ψ μ₂ b c • ∑ a : ι, ψ μ₁ a c • scatterOp car b a := by
      have hGq : ∀ q ∈ pairs,
          -((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0)) •
            (∑ a : ι, ψ μ₁ a c • scatterOp car (if q.1 = c then q.2 else q.1) a) =
          (if q.1 = c then ψ μ₂ q.2 c • ∑ a : ι, ψ μ₁ a c • scatterOp car q.2 a else 0) +
          (if q.2 = c then ψ μ₂ q.1 c • ∑ a : ι, ψ μ₁ a c • scatterOp car q.1 a else 0) := by
        intro q hq
        by_cases h1 : q.1 = c <;> by_cases h2 : q.2 = c
        · have hqq : q.1 = q.2 := h1.trans h2.symm
          exfalso; apply h_no_swap q hq
          have : (q.2, q.1) = q := Prod.ext hqq.symm hqq
          simpa [this] using hq
        · simp [h1, h2, h_anti μ₂ c q.2]
        · simp [h1, h2]
        · simp [h1, h2]
      rw [Finset.sum_congr rfl hGq]
      exact sum_pairs_contract_eq pairs h_no_swap h_cover c
        (fun b => ψ μ₂ b c • ∑ a : ι, ψ μ₁ a c • scatterOp car b a) (by simp [hdiag])
    rw [h_outer_q]
    simp_rw [Finset.smul_sum, smul_smul, mul_comm (ψ μ₂ _ c) (ψ μ₁ _ c)]
    exact Finset.sum_comm
  calc
    ∑ p ∈ pairs, ∑ q ∈ pairs, ∑ c : ι,
        (((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) *
         ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0))) •
        scatterOp car (if q.1 = c then q.2 else q.1) (if p.1 = c then p.2 else p.1)
      = ∑ p ∈ pairs, ∑ c : ι, ∑ q ∈ pairs,
          (((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) *
           ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0))) •
          scatterOp car (if q.1 = c then q.2 else q.1) (if p.1 = c then p.2 else p.1) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ c : ι, ∑ p ∈ pairs, ∑ q ∈ pairs,
          (((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) *
           ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0))) •
          scatterOp car (if q.1 = c then q.2 else q.1) (if p.1 = c then p.2 else p.1) :=
          Finset.sum_comm
    _ = ∑ c : ι, ∑ q ∈ pairs, ∑ p ∈ pairs,
          (((if p.1 = c then ψ μ₁ c p.2 else 0) + (if p.2 = c then -ψ μ₁ p.1 c else 0)) *
           ((if q.1 = c then ψ μ₂ c q.2 else 0) + (if q.2 = c then -ψ μ₂ q.1 c else 0))) •
          scatterOp car (if q.1 = c then q.2 else q.1) (if p.1 = c then p.2 else p.1) := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c : ι, ∑ a : ι, ∑ b : ι, (ψ μ₁ a c * ψ μ₂ b c) • scatterOp car b a := by
          refine Finset.sum_congr rfl fun c _ => hsum_c c
    _ = ∑ a : ι, ∑ b : ι, taniguchiGamma ψ μ₁ μ₂ a b • scatterOp car b a := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          dsimp [taniguchiGamma]
          rw [Finset.sum_smul]

/-- **Taniguchi Eq. (6a) Collective TDA Commutator Defect**:
`[X_{μ₁}, X_{μ₂}†] = δ_{μ₁ μ₂} - ∑ a b, Γ^{μ₁ μ₂}_{a b} a_b† a_a`. -/
theorem comm_tdaPhononAnn_tdaPhononCre_taniguchi_6a {ι_ph : Type*} [DecidableEq ι_ph]
    (car : QuasiparticleCAR ι A)
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (h_cover : ∀ a b : ι, a ≠ b → (a, b) ∈ pairs ∨ (b, a) ∈ pairs)
    (ψ : ι_ph → ι → ι → ℝ)
    (h_anti : ∀ μ a b, ψ μ b a = -ψ μ a b)
    (μ₁ μ₂ : ι_ph)
    (h_ortho : ∑ p ∈ pairs, ψ μ₁ p.1 p.2 * ψ μ₂ p.1 p.2 = if μ₁ = μ₂ then (1 : ℝ) else 0) :
    comm (tdaPhononAnn car pairs (ψ μ₁)) (tdaPhononCre car pairs (ψ μ₂)) =
      (if μ₁ = μ₂ then (1 : A) else 0) -
        ∑ a : ι, ∑ b : ι, taniguchiGamma ψ μ₁ μ₂ a b • scatterOp car b a := by
  dsimp [tdaPhononAnn, tdaPhononCre]
  change QuasiparticleCAR.comm _ _ = _
  rw [car.comm_tdaPairAnnihilation_tdaPairCreation_orthonormal pairs h_no_swap ψ μ₁ μ₂ h_ortho,
    tdaPairPauliDefect_eq_taniguchiGamma car pairs h_no_swap h_cover ψ h_anti μ₁ μ₂]
  split_ifs <;> simp

omit [Fintype ι] in
/-- Completeness reconstruction of `pairCre car b d` from complete antisymmetric TDA amplitudes. -/
theorem pairCre_eq_sum_tdaPhononCre {ι_ph : Type*} [Fintype ι_ph]
    (car : QuasiparticleCAR ι A)
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (h_cover : ∀ a b : ι, a ≠ b → (a, b) ∈ pairs ∨ (b, a) ∈ pairs)
    (ψ : ι_ph → ι → ι → ℝ)
    (h_complete : ∀ a b c d : ι,
      ∑ μ : ι_ph, ψ μ a b * ψ μ c d =
        (if a = c ∧ b = d then (1 : ℝ) else 0) - (if a = d ∧ b = c then 1 else 0))
    (b d : ι) :
    ∑ μ : ι_ph, ψ μ b d • tdaPhononCre car pairs (ψ μ) = pairCre car b d := by
  dsimp [tdaPhononCre, QuasiparticleCAR.tdaPairCreation]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hterm : ∀ p ∈ pairs,
      (∑ μ : ι_ph, (ψ μ b d * ψ μ p.1 p.2) • car.pairCreation p.1 p.2) =
        ((if b = p.1 ∧ d = p.2 then (1 : ℝ) else 0) -
          (if b = p.2 ∧ d = p.1 then 1 else 0)) • pairCre car p.1 p.2 := by
    intro p _
    rw [← Finset.sum_smul, h_complete b d p.1 p.2]
    rfl
  rw [Finset.sum_congr rfl hterm]
  by_cases hbd : b = d
  · subst hbd
    rw [show pairCre car b b = 0 from car.adag_sq b]
    refine Finset.sum_eq_zero fun p hp => ?_
    by_cases h1 : b = p.1 <;> by_cases h2 : b = p.2 <;> simp [h1, h2]
  · rcases h_cover b d hbd with hbd_in | hdb_in
    · have hnot : (d, b) ∉ pairs := h_no_swap (b, d) hbd_in
      rw [Finset.sum_eq_single (b, d)]
      · simp [hbd]
      · intro p hp hpne
        have hne1 : ¬(b = p.1 ∧ d = p.2) := fun ⟨h1, h2⟩ => hpne (Prod.ext h1.symm h2.symm)
        have hne2 : ¬(b = p.2 ∧ d = p.1) := fun ⟨h1, h2⟩ =>
          hnot (by have : p = (d, b) := Prod.ext h2.symm h1.symm; simpa [this] using hp)
        simp [hne1, hne2]
      · intro hm; exact False.elim (hm hbd_in)
    · have hnot : (b, d) ∉ pairs := h_no_swap (d, b) hdb_in
      rw [Finset.sum_eq_single (d, b)]
      · rw [show pairCre car b d = -pairCre car d b from car.pairCreation_swap d b]
        simp [hbd, Ne.symm hbd]
      · intro p hp hpne
        have hne1 : ¬(b = p.1 ∧ d = p.2) := fun ⟨h1, h2⟩ =>
          hnot (by have : p = (b, d) := Prod.ext h1.symm h2.symm; simpa [this] using hp)
        have hne2 : ¬(b = p.2 ∧ d = p.1) := fun ⟨h1, h2⟩ => hpne (Prod.ext h2.symm h1.symm)
        simp [hne1, hne2]
      · intro hm; exact False.elim (hm hdb_in)

/-- **Taniguchi Eq. (9) Collective Double-Commutator `Y`-Tensor Identity**:
`[[X_{μ₁}, X_{μ₂}†], X_{μ₃}†] = - ∑ μ', Y(μ₁, μ₂, μ₃, μ') • X_{μ'}†`. -/
theorem double_comm_tdaPhonon_taniguchi_9 {ι_ph : Type*} [Fintype ι_ph] [DecidableEq ι_ph]
    (car : QuasiparticleCAR ι A)
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (h_cover : ∀ a b : ι, a ≠ b → (a, b) ∈ pairs ∨ (b, a) ∈ pairs)
    (ψ : ι_ph → ι → ι → ℝ)
    (h_anti : ∀ μ a b, ψ μ b a = -ψ μ a b)
    (h_ortho : ∀ μ₁ μ₂, ∑ p ∈ pairs, ψ μ₁ p.1 p.2 * ψ μ₂ p.1 p.2 = if μ₁ = μ₂ then (1 : ℝ) else 0)
    (h_complete : ∀ a b c d : ι,
      ∑ μ : ι_ph, ψ μ a b * ψ μ c d =
        (if a = c ∧ b = d then (1 : ℝ) else 0) - (if a = d ∧ b = c then 1 else 0))
    (μ₁ μ₂ μ₃ : ι_ph) :
    comm (comm (tdaPhononAnn car pairs (ψ μ₁)) (tdaPhononCre car pairs (ψ μ₂)))
        (tdaPhononCre car pairs (ψ μ₃)) =
      -(∑ μ' : ι_ph, taniguchiY ψ μ₁ μ₂ μ₃ μ' • tdaPhononCre car pairs (ψ μ')) := by
  have hdiag : ∀ μ c, ψ μ c c = 0 := fun μ c => by
    have h := h_anti μ c c
    linarith
  rw [comm_tdaPhononAnn_tdaPhononCre_taniguchi_6a car pairs h_no_swap h_cover ψ h_anti μ₁ μ₂
    (h_ortho μ₁ μ₂)]
  have hcomm_sub : ∀ X Y Z : A, comm (X - Y) Z = comm X Z - comm Y Z := by
    intro X Y Z; dsimp [comm]; noncomm_ring
  have hcomm_one : ∀ Z : A, comm (1 : A) Z = 0 := by
    intro Z; dsimp [comm]; simp
  have hcomm_zero : ∀ Z : A, comm (0 : A) Z = 0 := by
    intro Z; dsimp [comm]; simp
  have h_scal : comm (if μ₁ = μ₂ then (1 : A) else 0) (tdaPhononCre car pairs (ψ μ₃)) = 0 := by
    split_ifs <;> simp [hcomm_one, hcomm_zero]
  rw [hcomm_sub, h_scal, zero_sub]
  congr 1
  have hcomm_sum_right : ∀ (s : Finset (ι × ι)) (X : A) (f : ι × ι → A),
      comm X (∑ x ∈ s, f x) = ∑ x ∈ s, comm X (f x) := by
    intro s X f
    dsimp [comm]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hcomm_smul_right : ∀ (r : ℝ) (X Y : A), comm X (r • Y) = r • comm X Y := by
    intro r X Y; dsimp [comm]; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  have hcomm_sum_l_1 :
      comm (∑ a : ι, ∑ b : ι, taniguchiGamma ψ μ₁ μ₂ a b • scatterOp car b a)
          (tdaPhononCre car pairs (ψ μ₃)) =
        ∑ a : ι, comm (∑ b : ι, taniguchiGamma ψ μ₁ μ₂ a b • scatterOp car b a)
          (tdaPhononCre car pairs (ψ μ₃)) := by
    dsimp [comm]; rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hcomm_sum_l_2 : ∀ a : ι,
      comm (∑ b : ι, taniguchiGamma ψ μ₁ μ₂ a b • scatterOp car b a)
          (tdaPhononCre car pairs (ψ μ₃)) =
        ∑ b : ι, taniguchiGamma ψ μ₁ μ₂ a b •
          comm (scatterOp car b a) (tdaPhononCre car pairs (ψ μ₃)) := by
    intro a
    dsimp [comm]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  rw [hcomm_sum_l_1]
  simp_rw [hcomm_sum_l_2]
  have h_scatter_tda : ∀ a b : ι,
      comm (scatterOp car b a) (tdaPhononCre car pairs (ψ μ₃)) =
        ∑ d : ι, ψ μ₃ a d • pairCre car b d := by
    intro a b
    dsimp [tdaPhononCre, QuasiparticleCAR.tdaPairCreation]
    rw [hcomm_sum_right]
    have hp_term : ∀ p ∈ pairs,
        comm (scatterOp car b a) (ψ μ₃ p.1 p.2 • car.pairCreation p.1 p.2) =
          (if p.1 = a then ψ μ₃ a p.2 • pairCre car b p.2 else 0) +
            (if p.2 = a then (-ψ μ₃ p.1 a) • pairCre car b p.1 else 0) := by
      intro p hp
      rw [hcomm_smul_right]
      change ψ μ₃ p.1 p.2 • comm (scatterOp car b a) (pairCre car p.1 p.2) = _
      rw [comm_scatterOp_pairCre, smul_sub]
      by_cases h1 : p.1 = a <;> by_cases h2 : p.2 = a
      · have hpp : p.1 = p.2 := h1.trans h2.symm
        exfalso; apply h_no_swap p hp
        have : (p.2, p.1) = p := Prod.ext hpp.symm hpp
        simpa [this] using hp
      · simp [h1, h2, Ne.symm h2]
      · simp [h1, h2, Ne.symm h1, neg_smul]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
    rw [Finset.sum_congr rfl hp_term, Finset.sum_add_distrib]
    have hd_split : ∀ p ∈ pairs,
        (if p.1 = a then ψ μ₃ a p.2 • pairCre car b p.2 else 0) +
          (if p.2 = a then (-ψ μ₃ p.1 a) • pairCre car b p.1 else 0) =
        ∑ d : ι,
          ((if p = (a, d) then ψ μ₃ a d • pairCre car b d else 0) +
           (if p = (d, a) then (-ψ μ₃ d a) • pairCre car b d else 0)) := by
      intro p hp
      by_cases h1 : p.1 = a <;> by_cases h2 : p.2 = a
      · have hpp : p.1 = p.2 := h1.trans h2.symm
        exfalso; apply h_no_swap p hp
        have : (p.2, p.1) = p := Prod.ext hpp.symm hpp
        simpa [this] using hp
      · simp only [h1, ↓reduceIte, h2, add_zero]
        rw [Finset.sum_eq_single p.2]
        · simp [Prod.ext_iff, h1, Ne.symm h2]
        · intro d _ hdp; simp [Prod.ext_iff, hdp.symm, h2]
        · intro hm; exact False.elim (hm (Finset.mem_univ _))
      · simp only [h1, ↓reduceIte, h2, zero_add]
        rw [Finset.sum_eq_single p.1]
        · simp [Prod.ext_iff, h2, Ne.symm h1]
        · intro d _ hdp; simp [Prod.ext_iff, h1, hdp.symm]
        · intro hm; exact False.elim (hm (Finset.mem_univ _))
      · simp only [h1, ↓reduceIte, h2, add_zero]
        refine (Finset.sum_eq_zero fun d _ => ?_).symm
        simp [Prod.ext_iff, h1, h2]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hd_split, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hda : d = a
    · subst hda; simp [hdiag]
    · rcases h_cover a d (Ne.symm hda) with had_in | hda_in
      · have hnot : (d, a) ∉ pairs := h_no_swap (a, d) had_in
        rw [Finset.sum_eq_single (a, d)]
        · have hne : (a, d) ≠ (d, a) := fun h => hda (congrArg Prod.fst h).symm
          simp [hne]
        · intro p hp hpne
          have hp1 : p ≠ (d, a) := fun h => hnot (h ▸ hp)
          simp [hp1, hpne]
        · intro hm; exact False.elim (hm had_in)
      · have hnot : (a, d) ∉ pairs := h_no_swap (d, a) hda_in
        rw [Finset.sum_eq_single (d, a)]
        · have hne : (d, a) ≠ (a, d) := fun h => hda (congrArg Prod.fst h)
          simp [hne, h_anti μ₃ d a]
        · intro p hp hpne
          have hp2 : p ≠ (a, d) := fun h => hnot (h ▸ hp)
          simp [hp2, hpne]
        · intro hm; exact False.elim (hm hda_in)
  simp_rw [h_scatter_tda, Finset.smul_sum, smul_smul]
  have h_sub_cre : ∀ a b d : ι,
      (taniguchiGamma ψ μ₁ μ₂ a b * ψ μ₃ a d) • pairCre car b d =
        ∑ μ' : ι_ph, (taniguchiGamma ψ μ₁ μ₂ a b * (ψ μ₃ a d * ψ μ' b d)) •
          tdaPhononCre car pairs (ψ μ') := by
    intro a b d
    rw [← pairCre_eq_sum_tdaPhononCre car pairs h_no_swap h_cover ψ h_complete b d,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun μ' _ => ?_
    rw [smul_smul, mul_assoc]
  simp_rw [h_sub_cre]
  calc
    ∑ a : ι, ∑ b : ι, ∑ d : ι, ∑ μ' : ι_ph,
        (taniguchiGamma ψ μ₁ μ₂ a b * (ψ μ₃ a d * ψ μ' b d)) •
          tdaPhononCre car pairs (ψ μ')
      = ∑ a : ι, ∑ b : ι, ∑ μ' : ι_ph, ∑ d : ι,
          (taniguchiGamma ψ μ₁ μ₂ a b * (ψ μ₃ a d * ψ μ' b d)) •
            tdaPhononCre car pairs (ψ μ') := by
          refine Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a : ι, ∑ μ' : ι_ph, ∑ b : ι, ∑ d : ι,
          (taniguchiGamma ψ μ₁ μ₂ a b * (ψ μ₃ a d * ψ μ' b d)) •
            tdaPhononCre car pairs (ψ μ') := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ μ' : ι_ph, ∑ a : ι, ∑ b : ι, ∑ d : ι,
          (taniguchiGamma ψ μ₁ μ₂ a b * (ψ μ₃ a d * ψ μ' b d)) •
            tdaPhononCre car pairs (ψ μ') :=
          Finset.sum_comm
    _ = ∑ μ' : ι_ph, taniguchiY ψ μ₁ μ₂ μ₃ μ' • tdaPhononCre car pairs (ψ μ') := by
          refine Finset.sum_congr rfl fun μ' _ => ?_
          dsimp [taniguchiY, taniguchiGamma]
          simp_rw [Finset.mul_sum, Finset.sum_smul]

end CollectiveTaniguchi

/-! ### Pauli-Blocking / Seniority Defect Theorem -/

section PauliBlocking

omit [Algebra ℝ A] in
/-- On any quasiparticle vacuum projector/element `vac : A` (`∀ p, car.a p * vac = 0`),
every scattering operator annihilates `vac`. -/
theorem scatterOp_mul_vac_eq_zero (car : QuasiparticleCAR ι A) (vac : A)
    (hvac : ∀ p, car.a p * vac = 0) (p q : ι) :
    scatterOp car p q * vac = 0 := by
  dsimp [scatterOp]
  rw [mul_assoc, hvac q, mul_zero]

omit [Algebra ℝ A] in
/-- On `vac : A`, every `pairPauliDefect` vanishes, so `[B_{ij}, B_{kl}†] vac = (δ_{ik}δ_{jl} - δ_{il}δ_{jk}) vac`. -/
theorem pairPauliDefect_mul_vac_eq_zero (car : QuasiparticleCAR ι A) (vac : A)
    (hvac : ∀ p, car.a p * vac = 0) (i j k l : ι) :
    car.pairPauliDefect i j k l * vac = 0 := by
  dsimp [QuasiparticleCAR.pairPauliDefect]
  simp only [sub_mul, add_mul]
  split_ifs <;> simp only [zero_mul, mul_assoc, hvac, mul_zero, sub_zero, add_zero]

omit [Algebra ℝ A] in
/-- On `vac : A`, the diagonal pair commutator `[B_{ij}, B_{ij}†]` acts as `+1` for `i ≠ j`. -/
theorem comm_pairAnn_pairCre_same_mul_vac (car : QuasiparticleCAR ι A) (vac : A)
    (hvac : ∀ p, car.a p * vac = 0) {i j : ι} (hij : i ≠ j) :
    comm (pairAnn car i j) (pairCre car i j) * vac = vac := by
  change QuasiparticleCAR.comm (car.pairAnnihilation i j) (car.pairCreation i j) * vac = vac
  rw [car.comm_pairAnnihilation_pairCreation_same i j hij, sub_mul, one_mul, add_mul]
  have hi : car.numberOp i * vac = 0 := by
    dsimp [QuasiparticleCAR.numberOp]; rw [mul_assoc, hvac i, mul_zero]
  have hj : car.numberOp j * vac = 0 := by
    dsimp [QuasiparticleCAR.numberOp]; rw [mul_assoc, hvac j, mul_zero]
  rw [hi, hj, add_zero, sub_zero]

omit [Algebra ℝ A] in
/-- Action of `car.numberOp p` on a 1-quasiparticle blocked state `car.adag b * vac`. -/
theorem numberOp_mul_adag_vac_same (car : QuasiparticleCAR ι A) (vac : A)
    (hvac : ∀ p, car.a p * vac = 0) (b : ι) :
    car.numberOp b * (car.adag b * vac) = car.adag b * vac := by
  dsimp [QuasiparticleCAR.numberOp]
  calc
    (car.adag b * car.a b) * (car.adag b * vac)
      = car.adag b * ((car.a b * car.adag b) * vac) := by simp only [mul_assoc]
    _ = car.adag b * ((1 - car.adag b * car.a b) * vac) := by rw [car.a_mul_adag_same b]
    _ = car.adag b * (vac - car.adag b * (car.a b * vac)) := by
          rw [sub_mul, one_mul, mul_assoc]
    _ = car.adag b * vac := by rw [hvac b, mul_zero, sub_zero]

omit [Algebra ℝ A] in
theorem numberOp_mul_adag_vac_ne (car : QuasiparticleCAR ι A) (vac : A)
    (hvac : ∀ p, car.a p * vac = 0) {p b : ι} (hpb : p ≠ b) :
    car.numberOp p * (car.adag b * vac) = 0 := by
  dsimp [QuasiparticleCAR.numberOp]
  calc
    (car.adag p * car.a p) * (car.adag b * vac)
      = car.adag p * ((car.a p * car.adag b) * vac) := by simp only [mul_assoc]
    _ = car.adag p * ((-(car.adag b * car.a p)) * vac) := by
          rw [car.a_mul_adag_distinct p b hpb]
    _ = -car.adag p * (car.adag b * (car.a p * vac)) := by noncomm_ring
    _ = 0 := by rw [hvac p, mul_zero, mul_zero]

omit [Algebra ℝ A] in
/-- **Pauli-Blocking / Seniority-1 Defect Theorem**:
On a blocked 1-quasiparticle state `ψ_b = car.adag b * vac`:
1. If `b = i ∨ b = j`, the Pauli-blocking defect equals `+ψ_b` and shifts the diagonal pair
   commutator `[B_{ij}, B_{ij}†] ψ_b` by `-1` from `ψ_b` to `0` (Pauli blocking).
2. If `b ≠ i ∧ b ≠ j`, the Pauli-blocking defect vanishes and `[B_{ij}, B_{ij}†] ψ_b = ψ_b`. -/
theorem pauli_blocking_defect_on_one_qp_state (car : QuasiparticleCAR ι A) (vac : A)
    (hvac : ∀ p, car.a p * vac = 0) {i j : ι} (hij : i ≠ j) (b : ι) :
    (b = i ∨ b = j →
      car.pairPauliDefect i j i j * (car.adag b * vac) = car.adag b * vac ∧
      comm (pairAnn car i j) (pairCre car i j) * (car.adag b * vac) = 0) ∧
    (b ≠ i ∧ b ≠ j →
      car.pairPauliDefect i j i j * (car.adag b * vac) = 0 ∧
      comm (pairAnn car i j) (pairCre car i j) * (car.adag b * vac) = car.adag b * vac) := by
  have hdef : car.pairPauliDefect i j i j = car.numberOp i + car.numberOp j :=
    car.pairPauliDefect_same i j hij
  have hcomm : comm (pairAnn car i j) (pairCre car i j) =
      1 - (car.numberOp i + car.numberOp j) := by
    change QuasiparticleCAR.comm (car.pairAnnihilation i j) (car.pairCreation i j) =
      1 - (car.numberOp i + car.numberOp j)
    exact car.comm_pairAnnihilation_pairCreation_same i j hij
  constructor
  · intro hb
    have hact : (car.numberOp i + car.numberOp j) * (car.adag b * vac) = car.adag b * vac := by
      rw [add_mul]
      rcases hb with rfl | rfl
      · rw [numberOp_mul_adag_vac_same car vac hvac b,
          numberOp_mul_adag_vac_ne car vac hvac hij.symm, add_zero]
      · rw [numberOp_mul_adag_vac_ne car vac hvac hij,
          numberOp_mul_adag_vac_same car vac hvac b, zero_add]
    refine ⟨by rw [hdef, hact], ?_⟩
    rw [hcomm, sub_mul, one_mul, hact, sub_self]
  · rintro ⟨hbi, hbj⟩
    have hact : (car.numberOp i + car.numberOp j) * (car.adag b * vac) = 0 := by
      rw [add_mul, numberOp_mul_adag_vac_ne car vac hvac hbi.symm,
        numberOp_mul_adag_vac_ne car vac hvac hbj.symm, add_zero]
    refine ⟨by rw [hdef, hact], ?_⟩
    rw [hcomm, sub_mul, one_mul, hact, sub_zero]

end PauliBlocking

/-! ### Finite-Mode Symmetric RPA Krein Orthogonality, Goldstone Zero-Mode Decoupling,
    & Finite-Matrix Boson CCR No-Go Bridge -/

section GoldstoneZeroModeDecoupling

/-- Finite-mode symmetric RPA eigenproblem: `A X + B Y = ω X` and `B X + A Y = -ω Y`. -/
def rpaEigenmode {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (ω : ℝ) (X Y : Fin m → ℝ) : Prop :=
  A *ᵥ X + B *ᵥ Y = ω • X ∧ B *ᵥ X + A *ᵥ Y = -(ω • Y)

/-- Indefinite Krein inner product `⟨X₁, X₂⟩ - ⟨Y₁, Y₂⟩`. -/
def kreinInner {m : ℕ} (X₁ Y₁ X₂ Y₂ : Fin m → ℝ) : ℝ :=
  dotProduct X₁ X₂ - dotProduct Y₁ Y₂

/-- **Krein Orthogonality of Distinct RPA Modes**:
If `Aᵀ = A`, `Bᵀ = B`, and `(X₁, Y₁)`, `(X₂, Y₂)` solve the symmetric RPA eigenproblem at
frequencies `ω₁ ≠ ω₂`, then `⟨X₁, X₂⟩ - ⟨Y₁, Y₂⟩ = 0`. -/
theorem rpa_krein_orthogonality {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : Aᵀ = A) (hB : Bᵀ = B)
    {ω₁ ω₂ : ℝ} {X₁ Y₁ X₂ Y₂ : Fin m → ℝ}
    (h1 : rpaEigenmode A B ω₁ X₁ Y₁)
    (h2 : rpaEigenmode A B ω₂ X₂ Y₂)
    (hne : ω₁ ≠ ω₂) :
    kreinInner X₁ Y₁ X₂ Y₂ = 0 := by
  have hlhs : dotProduct X₁ (A *ᵥ X₂ + B *ᵥ Y₂) + dotProduct Y₁ (B *ᵥ X₂ + A *ᵥ Y₂) =
      ω₂ * kreinInner X₁ Y₁ X₂ Y₂ := by
    rw [h2.1, h2.2]
    simp only [dotProduct_smul, dotProduct_neg, smul_eq_mul, kreinInner]
    rw [mul_sub, sub_eq_add_neg]
  have hrhs : dotProduct X₁ (A *ᵥ X₂ + B *ᵥ Y₂) + dotProduct Y₁ (B *ᵥ X₂ + A *ᵥ Y₂) =
      ω₁ * kreinInner X₁ Y₁ X₂ Y₂ := by
    have hXA : dotProduct X₁ (A *ᵥ X₂) = dotProduct (A *ᵥ X₁) X₂ := by
      calc
        X₁ ⬝ᵥ (A *ᵥ X₂) = (X₁ ᵥ* A) ⬝ᵥ X₂ := Matrix.dotProduct_mulVec X₁ A X₂
        _ = (Aᵀ *ᵥ X₁) ⬝ᵥ X₂ := by rw [Matrix.mulVec_transpose]
        _ = (A *ᵥ X₁) ⬝ᵥ X₂ := by rw [hA]
    have hXB : dotProduct X₁ (B *ᵥ Y₂) = dotProduct (B *ᵥ X₁) Y₂ := by
      calc
        X₁ ⬝ᵥ (B *ᵥ Y₂) = (X₁ ᵥ* B) ⬝ᵥ Y₂ := Matrix.dotProduct_mulVec X₁ B Y₂
        _ = (Bᵀ *ᵥ X₁) ⬝ᵥ Y₂ := by rw [Matrix.mulVec_transpose]
        _ = (B *ᵥ X₁) ⬝ᵥ Y₂ := by rw [hB]
    have hYB : dotProduct Y₁ (B *ᵥ X₂) = dotProduct (B *ᵥ Y₁) X₂ := by
      calc
        Y₁ ⬝ᵥ (B *ᵥ X₂) = (Y₁ ᵥ* B) ⬝ᵥ X₂ := Matrix.dotProduct_mulVec Y₁ B X₂
        _ = (Bᵀ *ᵥ Y₁) ⬝ᵥ X₂ := by rw [Matrix.mulVec_transpose]
        _ = (B *ᵥ Y₁) ⬝ᵥ X₂ := by rw [hB]
    have hYA : dotProduct Y₁ (A *ᵥ Y₂) = dotProduct (A *ᵥ Y₁) Y₂ := by
      calc
        Y₁ ⬝ᵥ (A *ᵥ Y₂) = (Y₁ ᵥ* A) ⬝ᵥ Y₂ := Matrix.dotProduct_mulVec Y₁ A Y₂
        _ = (Aᵀ *ᵥ Y₁) ⬝ᵥ Y₂ := by rw [Matrix.mulVec_transpose]
        _ = (A *ᵥ Y₁) ⬝ᵥ Y₂ := by rw [hA]
    simp only [dotProduct_add]
    rw [hXA, hXB, hYB, hYA]
    have hsum : (A *ᵥ X₁ ⬝ᵥ X₂ + B *ᵥ X₁ ⬝ᵥ Y₂) + (B *ᵥ Y₁ ⬝ᵥ X₂ + A *ᵥ Y₁ ⬝ᵥ Y₂) =
        (A *ᵥ X₁ + B *ᵥ Y₁) ⬝ᵥ X₂ + (B *ᵥ X₁ + A *ᵥ Y₁) ⬝ᵥ Y₂ := by
      simp only [add_dotProduct]
      abel
    rw [hsum, h1.1, h1.2]
    simp only [smul_dotProduct, neg_dotProduct, smul_eq_mul, kreinInner]
    rw [mul_sub, sub_eq_add_neg]
  have hdiff : (ω₁ - ω₂) * kreinInner X₁ Y₁ X₂ Y₂ = 0 := by linarith
  exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne)

/-- **Goldstone Zero-Mode Krein Orthogonality**:
Every nonzero-frequency RPA mode (`ω ≠ 0`) is Krein-orthogonal to every zero-frequency mode
(`A X₀ + B Y₀ = 0`, `B X₀ + A Y₀ = 0`). -/
theorem rpa_zero_mode_krein_orthogonality {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : Aᵀ = A) (hB : Bᵀ = B)
    {ω : ℝ} {X₁ Y₁ X₀ Y₀ : Fin m → ℝ}
    (h1 : rpaEigenmode A B ω X₁ Y₁)
    (hω : ω ≠ 0)
    (h0_1 : A *ᵥ X₀ + B *ᵥ Y₀ = 0)
    (h0_2 : B *ᵥ X₀ + A *ᵥ Y₀ = 0) :
    kreinInner X₁ Y₁ X₀ Y₀ = 0 := by
  apply rpa_krein_orthogonality hA hB h1 _ hω
  exact ⟨by simpa using h0_1, by simpa using h0_2⟩

/-- Any zero-mode `(X₀, Y₀)` satisfies `(A + B) *ᵥ (X₀ + Y₀) = 0` and `(A - B) *ᵥ (X₀ - Y₀) = 0`,
and has vanishing Krein norm whenever `X₀ = Y₀` or `X₀ = -Y₀` (in particular whenever `A + B`
or `A - B` is invertible). -/
theorem rpa_zero_mode_sum_diff {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    {X₀ Y₀ : Fin m → ℝ}
    (h0_1 : A *ᵥ X₀ + B *ᵥ Y₀ = 0)
    (h0_2 : B *ᵥ X₀ + A *ᵥ Y₀ = 0) :
    (A + B) *ᵥ (X₀ + Y₀) = 0 ∧ (A - B) *ᵥ (X₀ - Y₀) = 0 := by
  constructor
  · calc
      (A + B) *ᵥ (X₀ + Y₀) = (A *ᵥ X₀ + B *ᵥ Y₀) + (B *ᵥ X₀ + A *ᵥ Y₀) := by
        simp only [Matrix.add_mulVec, Matrix.mulVec_add]; abel
      _ = 0 := by rw [h0_1, h0_2, add_zero]
  · calc
      (A - B) *ᵥ (X₀ - Y₀) = (A *ᵥ X₀ + B *ᵥ Y₀) - (B *ᵥ X₀ + A *ᵥ Y₀) := by
        simp only [Matrix.sub_mulVec, Matrix.mulVec_sub]; abel
      _ = 0 := by rw [h0_1, h0_2, sub_self]

theorem kreinInner_self_eq_zero_of_eq_or_neg {m : ℕ} {X₀ Y₀ : Fin m → ℝ}
    (h : X₀ = Y₀ ∨ X₀ = -Y₀) :
    kreinInner X₀ Y₀ X₀ Y₀ = 0 := by
  rcases h with rfl | rfl
  · simp [kreinInner]
  · simp [kreinInner, dotProduct_neg, neg_dotProduct]

theorem rpa_zero_mode_krein_norm_zero_of_invertible_sum {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) ℝ} {X₀ Y₀ : Fin m → ℝ}
    (h0_1 : A *ᵥ X₀ + B *ᵥ Y₀ = 0)
    (h0_2 : B *ᵥ X₀ + A *ᵥ Y₀ = 0)
    (hdet : (A + B).det ≠ 0) :
    Y₀ = -X₀ ∧ kreinInner X₀ Y₀ X₀ Y₀ = 0 := by
  have hsum := (rpa_zero_mode_sum_diff A B h0_1 h0_2).1
  have hunit : IsUnit (A + B).det := isUnit_iff_ne_zero.mpr hdet
  have hxy : X₀ + Y₀ = 0 := by
    have := congrArg (fun v => (A + B)⁻¹ *ᵥ v) hsum
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  have hy : Y₀ = -X₀ := eq_neg_of_add_eq_zero_right hxy
  refine ⟨hy, ?_⟩
  rw [hy]
  simp [kreinInner, dotProduct_neg, neg_dotProduct]

theorem rpa_zero_mode_krein_norm_zero_of_invertible_diff {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) ℝ} {X₀ Y₀ : Fin m → ℝ}
    (h0_1 : A *ᵥ X₀ + B *ᵥ Y₀ = 0)
    (h0_2 : B *ᵥ X₀ + A *ᵥ Y₀ = 0)
    (hdet : (A - B).det ≠ 0) :
    X₀ = Y₀ ∧ kreinInner X₀ Y₀ X₀ Y₀ = 0 := by
  have hdiff := (rpa_zero_mode_sum_diff A B h0_1 h0_2).2
  have hunit : IsUnit (A - B).det := isUnit_iff_ne_zero.mpr hdet
  have hxy : X₀ - Y₀ = 0 := by
    have := congrArg (fun v => (A - B)⁻¹ *ᵥ v) hdiff
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  have hx : X₀ = Y₀ := sub_eq_zero.mp hxy
  refine ⟨hx, ?_⟩
  rw [hx]
  simp [kreinInner]

/-- Bogoliubov RPA annihilation phonon `Q(X, Y) = ∑ i, (X i • Q_i - Y i • Q_i†)` in `PhononRPA`. -/
def PhononRPA.bogoAnn {m : ℕ} (rpa : PhononRPA (Fin m) A) (X Y : Fin m → ℝ) : A :=
  ∑ i : Fin m, (X i • rpa.Q i - Y i • rpa.Qdag i)

/-- Bogoliubov RPA creation phonon `Q†(X, Y) = ∑ i, (X i • Q_i† - Y i • Q_i)` in `PhononRPA`. -/
def PhononRPA.bogoCre {m : ℕ} (rpa : PhononRPA (Fin m) A) (X Y : Fin m → ℝ) : A :=
  ∑ i : Fin m, (X i • rpa.Qdag i - Y i • rpa.Q i)

/-- Exact CCR bracket of two Bogoliubov RPA modes equals their Krein inner product. -/
theorem PhononRPA.comm_bogoAnn_bogoCre {m : ℕ} (rpa : PhononRPA (Fin m) A)
    (X₁ Y₁ X₂ Y₂ : Fin m → ℝ) :
    comm (rpa.bogoAnn X₁ Y₁) (rpa.bogoCre X₂ Y₂) =
      (kreinInner X₁ Y₁ X₂ Y₂) • (1 : A) := by
  have hcomm_sum_l : ∀ (f : Fin m → A) (Z : A),
      comm (∑ i : Fin m, f i) Z = ∑ i : Fin m, comm (f i) Z := by
    intro f Z; dsimp [comm]; rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hcomm_sum_r : ∀ (Z : A) (f : Fin m → A),
      comm Z (∑ i : Fin m, f i) = ∑ i : Fin m, comm Z (f i) := by
    intro Z f; dsimp [comm]; rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hcomm_sub_l : ∀ U V W : A, comm (U - V) W = comm U W - comm V W := by
    intro U V W; dsimp [comm]; noncomm_ring
  have hcomm_sub_r : ∀ U V W : A, comm U (V - W) = comm U V - comm U W := by
    intro U V W; dsimp [comm]; noncomm_ring
  have hcomm_smul_l : ∀ (r : ℝ) (U W : A), comm (r • U) W = r • comm U W := by
    intro r U W; dsimp [comm]; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  have hcomm_smul_r : ∀ (r : ℝ) (U W : A), comm U (r • W) = r • comm U W := by
    intro r U W; dsimp [comm]; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  have hQdag_Q (i j : Fin m) :
      comm (rpa.Qdag i) (rpa.Q j) = -(if j = i then (1 : A) else 0) := by
    have h := rpa.comm_Q_Qdag j i
    dsimp [comm] at h ⊢
    rw [← h]
    abel
  dsimp [PhononRPA.bogoAnn, PhononRPA.bogoCre]
  rw [hcomm_sum_l]
  have h_i : ∀ i : Fin m,
      comm (X₁ i • rpa.Q i - Y₁ i • rpa.Qdag i)
        (∑ j : Fin m, (X₂ j • rpa.Qdag j - Y₂ j • rpa.Q j)) =
      (X₁ i * X₂ i - Y₁ i * Y₂ i) • (1 : A) := by
    intro i
    rw [hcomm_sum_r, Finset.sum_eq_single i]
    · simp_rw [hcomm_sub_l, hcomm_sub_r, hcomm_smul_l, hcomm_smul_r,
        rpa.comm_Q_Qdag i i, rpa.comm_Q_Q i i, rpa.comm_Qdag_Qdag i i, hQdag_Q i i]
      simp [smul_smul, sub_smul]
    · intro j _ hji
      simp_rw [hcomm_sub_l, hcomm_sub_r, hcomm_smul_l, hcomm_smul_r,
        rpa.comm_Q_Qdag i j, rpa.comm_Q_Q i j, rpa.comm_Qdag_Qdag i j, hQdag_Q i j]
      simp [hji, Ne.symm hji]
    · intro hm; exact False.elim (hm (Finset.mem_univ i))
  rw [Finset.sum_congr rfl fun i _ => h_i i, ← Finset.sum_smul]
  congr 1
  simp only [kreinInner, dotProduct, Finset.sum_sub_distrib]

/-- **Goldstone Zero-Mode Decoupling & Non-Bosonic Obstruction Theorem**:
In any nontrivial `PhononRPA (Fin m) A`, a Goldstone zero-mode `(X₀, Y₀)` with vanishing Krein
norm (e.g. from `(A + B).det ≠ 0` or `(A - B).det ≠ 0`) has:
1. `[Q₀, Q₀†] = 0 ≠ 1` (cannot satisfy the canonical `PhononRPA` normalization `[Q₀, Q₀†] = 1`),
2. `[Q₁, Q₀†] = 0` and `[Q₀, Q₁†] = 0` for every nonzero-frequency RPA mode `(X₁, Y₁)` (`ω ≠ 0`). -/
theorem rpa_zero_mode_decouples_from_phononRPA {m : ℕ} [Nontrivial A]
    (rpa : PhononRPA (Fin m) A)
    {A_mat B_mat : Matrix (Fin m) (Fin m) ℝ}
    (hA : A_matᵀ = A_mat) (hB : B_matᵀ = B_mat)
    {ω : ℝ} {X₁ Y₁ X₀ Y₀ : Fin m → ℝ}
    (h1 : rpaEigenmode A_mat B_mat ω X₁ Y₁) (hω : ω ≠ 0)
    (h0_1 : A_mat *ᵥ X₀ + B_mat *ᵥ Y₀ = 0)
    (h0_2 : B_mat *ᵥ X₀ + A_mat *ᵥ Y₀ = 0)
    (hnorm : kreinInner X₀ Y₀ X₀ Y₀ = 0) :
    comm (rpa.bogoAnn X₀ Y₀) (rpa.bogoCre X₀ Y₀) = 0 ∧
      comm (rpa.bogoAnn X₀ Y₀) (rpa.bogoCre X₀ Y₀) ≠ 1 ∧
      comm (rpa.bogoAnn X₁ Y₁) (rpa.bogoCre X₀ Y₀) = 0 ∧
      comm (rpa.bogoAnn X₀ Y₀) (rpa.bogoCre X₁ Y₁) = 0 := by
  have h00 : comm (rpa.bogoAnn X₀ Y₀) (rpa.bogoCre X₀ Y₀) = 0 := by
    rw [rpa.comm_bogoAnn_bogoCre, hnorm, zero_smul]
  have h10 : kreinInner X₁ Y₁ X₀ Y₀ = 0 :=
    rpa_zero_mode_krein_orthogonality hA hB h1 hω h0_1 h0_2
  have h01 : kreinInner X₀ Y₀ X₁ Y₁ = 0 := by
    calc
      kreinInner X₀ Y₀ X₁ Y₁ = kreinInner X₁ Y₁ X₀ Y₀ := by
        simp only [kreinInner, dotProduct_comm]
      _ = 0 := h10
  refine ⟨h00, ?_, ?_, ?_⟩
  · rw [h00]; exact zero_ne_one
  · rw [rpa.comm_bogoAnn_bogoCre, h10, zero_smul]
  · rw [rpa.comm_bogoAnn_bogoCre, h01, zero_smul]

/-- **Finite-Matrix `PhononRPA` No-Go Theorem**:
Bridging to `InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.no_exact_boson_ccr_fin`:
no nonzero finite `n × n` matrix algebra over any characteristic-zero field `K` can carry
an exact `PhononRPA ι (Matrix (Fin n) (Fin n) K)` realization when `Nonempty ι`. -/
theorem no_finite_matrix_phononRPA {ι K : Type*} [DecidableEq ι] [Nonempty ι]
    [Field K] [CharZero K] (n : ℕ) (hn : 0 < n) :
    IsEmpty (PhononRPA ι (Matrix (Fin n) (Fin n) K)) := by
  refine ⟨fun rpa => ?_⟩
  let i₀ : ι := Classical.arbitrary ι
  have hccr : InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.commutatorN
      (rpa.Q i₀) (rpa.Qdag i₀) = 1 := by
    simpa [InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.commutatorN, comm] using
      rpa.comm_Q_Qdag i₀ i₀
  exact InfoGeometry.Nuclear.NuclearPhononRPAAlgebra.no_exact_boson_ccr_fin n hn
    ⟨rpa.Q i₀, rpa.Qdag i₀, hccr⟩

end GoldstoneZeroModeDecoupling

end MicroscopicCARAndGoldstone

end InfoGeometry.Physics.NuclearPhononRPA
