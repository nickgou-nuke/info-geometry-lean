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

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Physics.NuclearQuasiparticleCAR

/-!
# Canonical Anticommutation Relations (CAR) for Nuclear Quasiparticles

This module formalizes the canonical fermionic algebra for nuclear quasiparticles:
1. **The CAR Structure**:
   $\{\alpha_i, \alpha_j\} = 0$, $\{\alpha_i^\dagger, \alpha_j^\dagger\} = 0$,
   $\{\alpha_i, \alpha_j^\dagger\} = \delta_{ij} \cdot 1$.
2. **Pauli Exclusion**: $\alpha_i^2 = 0$, $(\alpha_i^\dagger)^2 = 0$.
3. **Quasiparticle Occupation Idempotence**: $N_i = \alpha_i^\dagger \alpha_i$ satisfies $N_i^2 = N_i$.
4. **Number Operator Commutators**:
   $[N_i, \alpha_j^\dagger] = \delta_{ij} \alpha_i^\dagger$, $[N_i, \alpha_j] = -\delta_{ij} \alpha_i$.
5. **Free Quasiparticle Hamiltonian & Excitation Energies**:
   $H_{\text{qp}} = \sum_i \varepsilon_i \alpha_i^\dagger \alpha_i \implies [H_{\text{qp}}, \alpha_k^\dagger] = \varepsilon_k \alpha_k^\dagger$.

All proofs are complete in native Lean 4 with 0 `sorry`s.
-/

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Canonical Anticommutation Relations structure for nuclear quasiparticles. -/
structure QuasiparticleCAR (ι : Type*) [DecidableEq ι] (A : Type*) [Ring A] where
  a : ι → A
  adag : ι → A
  anticomm_a_a : ∀ i j, a i * a j + a j * a i = 0
  anticomm_adag_adag : ∀ i j, adag i * adag j + adag j * adag i = 0
  anticomm_a_adag : ∀ i j, a i * adag j + adag j * a i = if i = j then 1 else 0

theorem two_smul_real (x : A) : (2 : ℝ) • x = x + x := by
  have : (2 : ℝ) = 1 + 1 := by norm_num
  rw [this, add_smul, one_smul]

namespace QuasiparticleCAR

variable (car : QuasiparticleCAR ι A)

/-- Associative commutator. -/
def comm (X Y : A) : A := X * Y - Y * X

/-- Pauli exclusion for annihilation operators: $\alpha_i^2 = 0$. -/
theorem a_sq (i : ι) : car.a i * car.a i = 0 := by
  have h := car.anticomm_a_a i i
  have h_smul : (2 : ℝ) • (car.a i * car.a i) = 0 := by
    rw [two_smul_real, h]
  have h_half : (1 / 2 : ℝ) • ((2 : ℝ) • (car.a i * car.a i)) = (0 : A) := by
    rw [h_smul, smul_zero]
  rw [smul_smul] at h_half
  have h_one : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [h_one, one_smul] at h_half
  exact h_half

/-- Pauli exclusion for creation operators: $(\alpha_i^\dagger)^2 = 0$. -/
theorem adag_sq (i : ι) : car.adag i * car.adag i = 0 := by
  have h := car.anticomm_adag_adag i i
  have h_smul : (2 : ℝ) • (car.adag i * car.adag i) = 0 := by
    rw [two_smul_real, h]
  have h_half : (1 / 2 : ℝ) • ((2 : ℝ) • (car.adag i * car.adag i)) = (0 : A) := by
    rw [h_smul, smul_zero]
  rw [smul_smul] at h_half
  have h_one : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  rw [h_one, one_smul] at h_half
  exact h_half

omit [Algebra ℝ A] in
/-- Anticommutation relation for same index: $\alpha_i \alpha_i^\dagger = 1 - \alpha_i^\dagger \alpha_i$. -/
theorem a_mul_adag_same (i : ι) : car.a i * car.adag i = 1 - car.adag i * car.a i := by
  have h := car.anticomm_a_adag i i
  simp only [↓reduceIte] at h
  rw [← sub_eq_zero]
  calc car.a i * car.adag i - (1 - car.adag i * car.a i)
      = car.a i * car.adag i + car.adag i * car.a i - 1 := by abel
    _ = 1 - 1 := by rw [h]
    _ = 0 := sub_self 1

omit [Algebra ℝ A] in
/-- Anticommutation relation for distinct indices: $\alpha_i \alpha_j^\dagger = -\alpha_j^\dagger \alpha_i$. -/
theorem a_mul_adag_distinct (i j : ι) (hij : i ≠ j) :
    car.a i * car.adag j = - (car.adag j * car.a i) := by
  have h := car.anticomm_a_adag i j
  simp only [hij, ↓reduceIte] at h
  rw [← add_eq_zero_iff_eq_neg]
  exact h

omit [Algebra ℝ A] in
/-- Creation operator anticommutation: $\alpha_j^\dagger \alpha_i^\dagger = -\alpha_i^\dagger \alpha_j^\dagger$. -/
theorem adag_mul_adag_comm (i j : ι) :
    car.adag j * car.adag i = - (car.adag i * car.adag j) := by
  have h := car.anticomm_adag_adag j i
  rw [← add_eq_zero_iff_eq_neg]
  exact h

omit [Algebra ℝ A] in
/-- Quasiparticle number / occupation operator: $N_i = \alpha_i^\dagger \alpha_i$. -/
def numberOp (i : ι) : A :=
  car.adag i * car.a i

/-- **Theorem**: Quasiparticle occupation is idempotent: $N_i^2 = N_i$. -/
theorem numberOp_idempotent (i : ι) :
    car.numberOp i * car.numberOp i = car.numberOp i := by
  dsimp [numberOp]
  calc car.adag i * car.a i * (car.adag i * car.a i)
      = car.adag i * (car.a i * car.adag i) * car.a i := by
        simp only [mul_assoc]
    _ = car.adag i * (1 - car.adag i * car.a i) * car.a i := by
        rw [car.a_mul_adag_same i]
    _ = (car.adag i * 1 - car.adag i * (car.adag i * car.a i)) * car.a i := by
        rw [mul_sub]
    _ = (car.adag i - (car.adag i * car.adag i) * car.a i) * car.a i := by
        simp only [mul_one, mul_assoc]
    _ = (car.adag i - 0 * car.a i) * car.a i := by
        rw [car.adag_sq i]
    _ = car.adag i * car.a i := by
        simp only [zero_mul, sub_zero]

/-- **Theorem**: Number-Creation commutator: $[N_i, \alpha_i^\dagger] = \alpha_i^\dagger$. -/
theorem comm_numberOp_adag_same (i : ι) :
    comm (car.numberOp i) (car.adag i) = car.adag i := by
  dsimp [comm, numberOp]
  calc car.adag i * car.a i * car.adag i - car.adag i * (car.adag i * car.a i)
      = car.adag i * (car.a i * car.adag i) - (car.adag i * car.adag i) * car.a i := by
        simp only [mul_assoc]
    _ = car.adag i * (1 - car.adag i * car.a i) - 0 * car.a i := by
        rw [car.a_mul_adag_same i, car.adag_sq i]
    _ = car.adag i * 1 - car.adag i * (car.adag i * car.a i) - 0 := by
        rw [mul_sub, zero_mul]
    _ = car.adag i * 1 - (car.adag i * car.adag i) * car.a i - 0 := by
        simp only [mul_assoc]
    _ = car.adag i * 1 - 0 * car.a i - 0 := by
        rw [car.adag_sq i]
    _ = car.adag i := by
        simp only [mul_one, zero_mul, sub_zero]

omit [Algebra ℝ A] in
/-- **Theorem**: Number-Creation commutator for distinct modes: $[N_i, \alpha_j^\dagger] = 0$. -/
theorem comm_numberOp_adag_distinct (i j : ι) (hij : i ≠ j) :
    comm (car.numberOp i) (car.adag j) = 0 := by
  dsimp [comm, numberOp]
  calc car.adag i * car.a i * car.adag j - car.adag j * (car.adag i * car.a i)
      = car.adag i * (car.a i * car.adag j) - (car.adag j * car.adag i) * car.a i := by
        simp only [mul_assoc]
    _ = car.adag i * (- (car.adag j * car.a i)) - (- (car.adag i * car.adag j)) * car.a i := by
        rw [car.a_mul_adag_distinct i j hij, car.adag_mul_adag_comm i j]
    _ = - (car.adag i * (car.adag j * car.a i)) - (- ((car.adag i * car.adag j) * car.a i)) := by
        simp only [mul_neg, neg_mul]
    _ = 0 := by
        simp only [mul_assoc, sub_neg_eq_add]
        abel

omit [Algebra ℝ A] in
/-- Number operators belonging to distinct modes commute with annihilation. -/
theorem comm_numberOp_a_distinct_carrier (i j : ι) (hij : i ≠ j) :
    comm (car.numberOp i) (car.a j) = 0 := by
  dsimp [comm, numberOp]
  have h₁ := car.anticomm_a_a i j
  have h₂ := car.anticomm_a_adag j i
  simp only [Ne.symm hij, ↓reduceIte] at h₂
  calc car.adag i * car.a i * car.a j - car.a j * (car.adag i * car.a i)
      = car.adag i * (car.a i * car.a j) -
          (car.a j * car.adag i) * car.a i := by
        simp only [mul_assoc]
    _ = car.adag i * (-(car.a j * car.a i)) -
          (-(car.adag i * car.a j)) * car.a i := by
        rw [show car.a i * car.a j = -(car.a j * car.a i) by
          exact eq_neg_of_add_eq_zero_left h₁]
        rw [show car.a j * car.adag i = -(car.adag i * car.a j) by
          exact eq_neg_of_add_eq_zero_left h₂]
    _ = 0 := by
      simp only [mul_neg, neg_mul, mul_assoc, sub_neg_eq_add]
      abel

/-- Free single-particle Hamiltonian for a finite mode set: $H_{\text{qp}} = \sum_{i \in s} \varepsilon_i N_i$. -/
def freeQuasiparticleHamiltonian (s : Finset ι) (eps : ι → ℝ) : A :=
  ∑ i ∈ s, (eps i) • car.numberOp i

/-- **Theorem**: Commutator of $H_{\text{qp}}$ with creation operator:
    $[H_{\text{qp}}, \alpha_k^\dagger] = \varepsilon_k \alpha_k^\dagger$. -/
theorem comm_freeQuasiparticleHamiltonian_adag (s : Finset ι) (eps : ι → ℝ) (k : ι) (hk : k ∈ s) :
    comm (car.freeQuasiparticleHamiltonian s eps) (car.adag k) = (eps k) • car.adag k := by
  dsimp [freeQuasiparticleHamiltonian, comm]
  have h_comm_sum : (∑ i ∈ s, (eps i) • car.numberOp i) * car.adag k -
                    car.adag k * (∑ i ∈ s, (eps i) • car.numberOp i) =
      ∑ i ∈ s, (eps i) • comm (car.numberOp i) (car.adag k) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [comm]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  rw [h_comm_sum]
  rw [Finset.sum_eq_single k]
  · rw [car.comm_numberOp_adag_same k]
  · intro j hj hjk
    rw [car.comm_numberOp_adag_distinct j k hjk, smul_zero]
  · intro hnk
    exact False.elim (hnk hk)

/-- The free Hamiltonian has the opposite weight on annihilation operators. -/
theorem comm_freeQuasiparticleHamiltonian_a (s : Finset ι) (eps : ι → ℝ) (k : ι) (hk : k ∈ s) :
    comm (car.freeQuasiparticleHamiltonian s eps) (car.a k) =
      - ((eps k) • car.a k) := by
  dsimp [freeQuasiparticleHamiltonian, comm]
  have h_comm_sum : (∑ i ∈ s, (eps i) • car.numberOp i) * car.a k -
                    car.a k * (∑ i ∈ s, (eps i) • car.numberOp i) =
      ∑ i ∈ s, (eps i) • comm (car.numberOp i) (car.a k) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [comm]
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  rw [h_comm_sum]
  rw [Finset.sum_eq_single k]
  · have h_same : comm (car.numberOp k) (car.a k) = - car.a k := by
      dsimp [comm, numberOp]
      calc car.adag k * car.a k * car.a k - car.a k * (car.adag k * car.a k)
          = car.adag k * (car.a k * car.a k) -
              (car.a k * car.adag k) * car.a k := by
            noncomm_ring
        _ = car.adag k * 0 - (1 - car.adag k * car.a k) * car.a k := by
            rw [car.a_sq k, car.a_mul_adag_same k]
        _ = - car.a k + (car.adag k * car.a k) * car.a k := by
            rw [sub_mul]
            simp only [mul_zero, one_mul, zero_sub]
            abel_nf
        _ = - car.a k := by
            rw [mul_assoc, car.a_sq k, mul_zero, add_zero]
    rw [h_same]
    exact smul_neg _ _
  · intro j hj hjk
    rw [car.comm_numberOp_a_distinct_carrier j k hjk, smul_zero]
  · intro hnk
    exact False.elim (hnk hk)

/-! ## Microscopic Two-Quasiparticle TDA Pair Operators & Exact QBA Defect -/

omit [Algebra ℝ A] in
/-- Two-quasiparticle pair annihilation operator $B_{ab} = \alpha_b \alpha_a$. -/
def pairAnnihilation (a b : ι) : A :=
  car.a b * car.a a

omit [Algebra ℝ A] in
/-- Two-quasiparticle pair creation operator $B_{ab}^\dagger = \alpha_a^\dagger \alpha_b^\dagger$. -/
def pairCreation (a b : ι) : A :=
  car.adag a * car.adag b

omit [Algebra ℝ A] in
/-- Exact fermion-exchange / Pauli-blocking defect appearing in $[B_{ab}, B_{cd}^\dagger]$. -/
def pairPauliDefect (a b c d : ι) : A :=
  (if a = c then car.adag d * car.a b else 0) -
    (if b = c then car.adag d * car.a a else 0) -
    (if a = d then car.adag c * car.a b else 0) +
    (if b = d then car.adag c * car.a a else 0)

omit [Algebra ℝ A] in
/-- Antisymmetry of pair annihilation under index swap. -/
theorem pairAnnihilation_swap (a b : ι) :
    car.pairAnnihilation b a = -car.pairAnnihilation a b := by
  dsimp [pairAnnihilation]
  exact eq_neg_of_add_eq_zero_left (car.anticomm_a_a a b)

omit [Algebra ℝ A] in
/-- Antisymmetry of pair creation under index swap. -/
theorem pairCreation_swap (a b : ι) :
    car.pairCreation b a = -car.pairCreation a b := by
  dsimp [pairCreation]
  exact car.adag_mul_adag_comm a b

omit [Algebra ℝ A] in
/-- Pair annihilation operators commute in any associative CAR ring. -/
theorem comm_pairAnnihilation_pairAnnihilation (a b c d : ι) :
    comm (car.pairAnnihilation a b) (car.pairAnnihilation c d) = 0 := by
  have haa (i j : ι) : car.a i * car.a j = -(car.a j * car.a i) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_a_a i j)
  dsimp [comm, pairAnnihilation]
  calc
    (car.a b * car.a a) * (car.a d * car.a c) -
        (car.a d * car.a c) * (car.a b * car.a a)
      = car.a b * ((car.a a * car.a d) * car.a c) -
          (car.a d * car.a c) * (car.a b * car.a a) := by noncomm_ring
    _ = car.a b * ((-(car.a d * car.a a)) * car.a c) -
          (car.a d * car.a c) * (car.a b * car.a a) := by rw [haa a d]
    _ = -(car.a b * car.a d * (car.a a * car.a c)) -
          (car.a d * car.a c) * (car.a b * car.a a) := by noncomm_ring
    _ = -(car.a b * car.a d * (-(car.a c * car.a a))) -
          (car.a d * car.a c) * (car.a b * car.a a) := by rw [haa a c]
    _ = ((car.a b * car.a d) * car.a c) * car.a a -
          (car.a d * car.a c) * (car.a b * car.a a) := by noncomm_ring
    _ = ((car.a b * car.a d) * car.a c) * car.a a -
          (car.a d * car.a c) * (car.a b * car.a a) := by noncomm_ring
    _ = ((-(car.a d * car.a b)) * car.a c) * car.a a -
          (car.a d * car.a c) * (car.a b * car.a a) := by rw [haa b d]
    _ = (-(car.a d * (car.a b * car.a c))) * car.a a -
          (car.a d * car.a c) * (car.a b * car.a a) := by noncomm_ring
    _ = (-(car.a d * (-(car.a c * car.a b)))) * car.a a -
          (car.a d * car.a c) * (car.a b * car.a a) := by rw [haa b c]
    _ = 0 := by noncomm_ring

omit [Algebra ℝ A] in
/-- Pair creation operators commute in any associative CAR ring. -/
theorem comm_pairCreation_pairCreation (a b c d : ι) :
    comm (car.pairCreation a b) (car.pairCreation c d) = 0 := by
  have hdd (i j : ι) : car.adag i * car.adag j = -(car.adag j * car.adag i) :=
    car.adag_mul_adag_comm j i
  dsimp [comm, pairCreation]
  calc
    (car.adag a * car.adag b) * (car.adag c * car.adag d) -
        (car.adag c * car.adag d) * (car.adag a * car.adag b)
      = car.adag a * ((car.adag b * car.adag c) * car.adag d) -
          (car.adag c * car.adag d) * (car.adag a * car.adag b) := by noncomm_ring
    _ = car.adag a * ((-(car.adag c * car.adag b)) * car.adag d) -
          (car.adag c * car.adag d) * (car.adag a * car.adag b) := by rw [hdd b c]
    _ = -(car.adag a * car.adag c * (car.adag b * car.adag d)) -
          (car.adag c * car.adag d) * (car.adag a * car.adag b) := by noncomm_ring
    _ = -(car.adag a * car.adag c * (-(car.adag d * car.adag b))) -
          (car.adag c * car.adag d) * (car.adag a * car.adag b) := by rw [hdd b d]
    _ = ((car.adag a * car.adag c) * car.adag d) * car.adag b -
          (car.adag c * car.adag d) * (car.adag a * car.adag b) := by noncomm_ring
    _ = ((-(car.adag c * car.adag a)) * car.adag d) * car.adag b -
          (car.adag c * car.adag d) * (car.adag a * car.adag b) := by rw [hdd a c]
    _ = (-(car.adag c * (car.adag a * car.adag d))) * car.adag b -
          (car.adag c * car.adag d) * (car.adag a * car.adag b) := by noncomm_ring
    _ = (-(car.adag c * (-(car.adag d * car.adag a)))) * car.adag b -
          (car.adag c * car.adag d) * (car.adag a * car.adag b) := by rw [hdd a d]
    _ = 0 := by noncomm_ring

omit [Algebra ℝ A] in
/-- Exact fermion-pair commutator $[B_{ab}, B_{cd}^\dagger]$ separating the bosonic
Kronecker scalar part from `pairPauliDefect a b c d`. -/
theorem comm_pairAnnihilation_pairCreation (a b c d : ι) :
    comm (car.pairAnnihilation a b) (car.pairCreation c d) =
      ((if a = c then (1 : A) else 0) * (if b = d then 1 else 0) -
        (if b = c then 1 else 0) * (if a = d then 1 else 0)) -
        car.pairPauliDefect a b c d := by
  have normalOrder (annihilator creator : ι) :
      car.a annihilator * car.adag creator =
        (if annihilator = creator then (1 : A) else 0) -
          car.adag creator * car.a annihilator :=
    eq_sub_of_add_eq (car.anticomm_a_adag annihilator creator)
  dsimp [comm, pairAnnihilation, pairCreation, pairPauliDefect]
  calc
    (car.a b * car.a a) * (car.adag c * car.adag d) -
        (car.adag c * car.adag d) * (car.a b * car.a a)
      = car.a b * (car.a a * car.adag c + car.adag c * car.a a) * car.adag d -
          (car.a b * car.adag c + car.adag c * car.a b) * car.a a * car.adag d +
          car.adag c * car.a b * (car.a a * car.adag d + car.adag d * car.a a) -
          car.adag c * (car.a b * car.adag d + car.adag d * car.a b) * car.a a := by
        noncomm_ring
    _ = _ := by
        rw [car.anticomm_a_adag, car.anticomm_a_adag,
          car.anticomm_a_adag, car.anticomm_a_adag]
        split_ifs <;> simp only [mul_one, one_mul, mul_zero, zero_mul]
        all_goals
          try rw [normalOrder b d]
          try rw [normalOrder a d]
          try split_ifs
          all_goals noncomm_ring

omit [Algebra ℝ A] in
/-- Diagonal Pauli-blocking defect reduces to `N_a + N_b` for distinct indices `a ≠ b`. -/
theorem pairPauliDefect_same (a b : ι) (hab : a ≠ b) :
    car.pairPauliDefect a b a b = car.numberOp a + car.numberOp b := by
  dsimp [pairPauliDefect, numberOp]
  simp [hab, Ne.symm hab]
  abel

omit [Algebra ℝ A] in
/-- Exact diagonal pair commutator $[B_{ab}, B_{ab}^\dagger] = 1 - (N_a + N_b)$ for `a ≠ b`. -/
theorem comm_pairAnnihilation_pairCreation_same (a b : ι) (hab : a ≠ b) :
    comm (car.pairAnnihilation a b) (car.pairCreation a b) =
      1 - (car.numberOp a + car.numberOp b) := by
  rw [car.comm_pairAnnihilation_pairCreation a b a b, car.pairPauliDefect_same a b hab]
  simp [hab, Ne.symm hab]

section TDALinearCombinations

variable {R : Type*} [CommRing R] [Algebra R A]

omit [Algebra ℝ A] in
private theorem comm_sum_smul {α β : Type*} (s : Finset α) (t : Finset β)
    (c : α → R) (d : β → R) (X : α → A) (Y : β → A) :
    comm (∑ p ∈ s, c p • X p) (∑ q ∈ t, d q • Y q) =
      ∑ p ∈ s, ∑ q ∈ t, (c p * d q) • comm (X p) (Y q) := by
  dsimp [comm]
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    smul_smul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_comm (d q) (c p), smul_sub]

omit [Algebra ℝ A] in
/-- Microscopic Tamm–Dancoff pair annihilation operator
$X_\mu = \sum_{(\alpha,\beta) \in \mathrm{pairs}} \psi(\alpha,\beta)\, \alpha_\beta \alpha_\alpha$. -/
def tdaPairAnnihilation (pairs : Finset (ι × ι)) (ψ : ι → ι → R) : A :=
  ∑ p ∈ pairs, ψ p.1 p.2 • car.pairAnnihilation p.1 p.2

omit [Algebra ℝ A] in
/-- Microscopic Tamm–Dancoff pair creation operator
$X_\mu^\dagger = \sum_{(\alpha,\beta) \in \mathrm{pairs}} \psi(\alpha,\beta)\, \alpha_\alpha^\dagger \alpha_\beta^\dagger$. -/
def tdaPairCreation (pairs : Finset (ι × ι)) (ψ : ι → ι → R) : A :=
  ∑ p ∈ pairs, ψ p.1 p.2 • car.pairCreation p.1 p.2

omit [Algebra ℝ A] in
/-- Exact Pauli-blocking defect operator for two TDA collective pair combinations. -/
def tdaPairPauliDefect (pairs₁ pairs₂ : Finset (ι × ι)) (ψ φ : ι → ι → R) : A :=
  ∑ p ∈ pairs₁, ∑ q ∈ pairs₂,
    (ψ p.1 p.2 * φ q.1 q.2) • car.pairPauliDefect p.1 p.2 q.1 q.2

omit [Algebra ℝ A] in
/-- Collective TDA pair annihilation operators commute identically. -/
theorem comm_tdaPairAnnihilation_self
    (pairs₁ pairs₂ : Finset (ι × ι)) (ψ φ : ι → ι → R) :
    comm (car.tdaPairAnnihilation pairs₁ ψ) (car.tdaPairAnnihilation pairs₂ φ) = 0 := by
  dsimp [tdaPairAnnihilation]
  rw [comm_sum_smul]
  simp [car.comm_pairAnnihilation_pairAnnihilation]

omit [Algebra ℝ A] in
/-- Collective TDA pair creation operators commute identically. -/
theorem comm_tdaPairCreation_self
    (pairs₁ pairs₂ : Finset (ι × ι)) (ψ φ : ι → ι → R) :
    comm (car.tdaPairCreation pairs₁ ψ) (car.tdaPairCreation pairs₂ φ) = 0 := by
  dsimp [tdaPairCreation]
  rw [comm_sum_smul]
  simp [car.comm_pairCreation_pairCreation]

omit [Algebra ℝ A] in
/-- Exact commutator $[X_\psi, X_\varphi^\dagger]$ for arbitrary microscopic TDA amplitudes
over any `[CommRing R]` and `[Algebra R A]`. -/
theorem comm_tdaPairAnnihilation_tdaPairCreation
    (pairs₁ pairs₂ : Finset (ι × ι)) (ψ φ : ι → ι → R) :
    comm (car.tdaPairAnnihilation pairs₁ ψ) (car.tdaPairCreation pairs₂ φ) =
      (∑ p ∈ pairs₁, ∑ q ∈ pairs₂,
        ψ p.1 p.2 * φ q.1 q.2 *
          ((if p.1 = q.1 then (1 : R) else 0) * (if p.2 = q.2 then 1 else 0) -
            (if p.2 = q.1 then 1 else 0) * (if p.1 = q.2 then 1 else 0))) • (1 : A) -
        car.tdaPairPauliDefect pairs₁ pairs₂ ψ φ := by
  dsimp [tdaPairAnnihilation, tdaPairCreation, tdaPairPauliDefect]
  rw [comm_sum_smul]
  have hterm : ∀ p ∈ pairs₁, ∀ q ∈ pairs₂,
      (ψ p.1 p.2 * φ q.1 q.2) • comm (car.pairAnnihilation p.1 p.2) (car.pairCreation q.1 q.2) =
        (ψ p.1 p.2 * φ q.1 q.2 *
          ((if p.1 = q.1 then (1 : R) else 0) * (if p.2 = q.2 then 1 else 0) -
            (if p.2 = q.1 then 1 else 0) * (if p.1 = q.2 then 1 else 0))) • (1 : A) -
        (ψ p.1 p.2 * φ q.1 q.2) • car.pairPauliDefect p.1 p.2 q.1 q.2 := by
    intro p _ q _
    rw [car.comm_pairAnnihilation_pairCreation, smul_sub]
    congr 1
    split_ifs <;> simp [mul_smul]
  calc
    ∑ p ∈ pairs₁, ∑ q ∈ pairs₂,
        (ψ p.1 p.2 * φ q.1 q.2) • comm (car.pairAnnihilation p.1 p.2) (car.pairCreation q.1 q.2)
      = ∑ p ∈ pairs₁, ∑ q ∈ pairs₂,
          ((ψ p.1 p.2 * φ q.1 q.2 *
            ((if p.1 = q.1 then (1 : R) else 0) * (if p.2 = q.2 then 1 else 0) -
              (if p.2 = q.1 then 1 else 0) * (if p.1 = q.2 then 1 else 0))) • (1 : A) -
          (ψ p.1 p.2 * φ q.1 q.2) • car.pairPauliDefect p.1 p.2 q.1 q.2) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            exact Finset.sum_congr rfl fun q hq => hterm p hp q hq
    _ = (∑ p ∈ pairs₁, ∑ q ∈ pairs₂,
          (ψ p.1 p.2 * φ q.1 q.2 *
            ((if p.1 = q.1 then (1 : R) else 0) * (if p.2 = q.2 then 1 else 0) -
              (if p.2 = q.1 then 1 else 0) * (if p.1 = q.2 then 1 else 0))) • (1 : A)) -
          ∑ p ∈ pairs₁, ∑ q ∈ pairs₂,
            (ψ p.1 p.2 * φ q.1 q.2) • car.pairPauliDefect p.1 p.2 q.1 q.2 := by
          simp only [Finset.sum_sub_distrib]
    _ = _ := by
          congr 1
          simp only [Finset.sum_smul]

omit [Algebra ℝ A] in
/-- For any oriented pair set `pairs` (containing no swapped pair `(b, a)` alongside `(a, b)`),
the cross-exchange scalar contraction vanishes and the scalar term is the inner product
`∑ p ∈ pairs, ψ p.1 p.2 * φ p.1 p.2`. -/
theorem comm_tdaPairAnnihilation_tdaPairCreation_oriented
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (ψ φ : ι → ι → R) :
    comm (car.tdaPairAnnihilation pairs ψ) (car.tdaPairCreation pairs φ) =
      (∑ p ∈ pairs, ψ p.1 p.2 * φ p.1 p.2) • (1 : A) -
        car.tdaPairPauliDefect pairs pairs ψ φ := by
  rw [car.comm_tdaPairAnnihilation_tdaPairCreation]
  congr 2
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · have hp12 : p.1 ≠ p.2 := by
      intro h
      apply h_no_swap p hp
      have : (p.2, p.1) = p := Prod.ext h.symm h
      simpa [this] using hp
    simp [hp12, hp12.symm]
  · intro q hq hqp
    have h1 : ¬ (p.1 = q.1 ∧ p.2 = q.2) := by
      rintro ⟨ha, hb⟩
      exact hqp (Prod.ext ha.symm hb.symm)
    have h2 : ¬ (p.2 = q.1 ∧ p.1 = q.2) := by
      rintro ⟨ha, hb⟩
      apply h_no_swap p hp
      have : q = (p.2, p.1) := Prod.ext ha.symm hb.symm
      simpa [this] using hq
    split_ifs <;> simp_all
  · intro hnp
    exact False.elim (hnp hp)

omit [Algebra ℝ A] in
/-- Under orthonormal oriented TDA amplitudes `∑ p ∈ pairs, ψ μ p.1 p.2 * ψ μ' p.1 p.2 = δ_{μμ'}`,
the commutator equals `δ_{μμ'} • 1 - tdaPairPauliDefect`. -/
theorem comm_tdaPairAnnihilation_tdaPairCreation_orthonormal
    {ι_ph : Type*} [DecidableEq ι_ph]
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (ψ : ι_ph → ι → ι → R) (μ μ' : ι_ph)
    (h_ortho : ∑ p ∈ pairs, ψ μ p.1 p.2 * ψ μ' p.1 p.2 = if μ = μ' then (1 : R) else 0) :
    comm (car.tdaPairAnnihilation pairs (ψ μ)) (car.tdaPairCreation pairs (ψ μ')) =
      (if μ = μ' then (1 : R) else 0) • (1 : A) -
        car.tdaPairPauliDefect pairs pairs (ψ μ) (ψ μ') := by
  rw [car.comm_tdaPairAnnihilation_tdaPairCreation_oriented pairs h_no_swap, h_ortho]

section VacuumQBA

variable {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

omit [Algebra ℝ A] in
/-- Any Fock-vacuum / zero-quasiparticle state (`∀ i, car.a i • v = 0`) is annihilated by
every microscopic Pauli-blocking defect. -/
theorem pairPauliDefect_smul_eq_zero (v : V) (hvac : ∀ i, car.a i • v = 0)
    (a b c d : ι) :
    car.pairPauliDefect a b c d • v = 0 := by
  dsimp [pairPauliDefect]
  simp only [sub_smul, add_smul]
  split_ifs <;>
    simp only [zero_smul, mul_smul, hvac, smul_zero, sub_zero, add_zero]

omit [Algebra ℝ A] in
/-- Collective TDA Pauli-blocking defect annihilates any Fock vacuum state. -/
theorem tdaPairPauliDefect_smul_eq_zero (v : V) (hvac : ∀ i, car.a i • v = 0)
    (pairs₁ pairs₂ : Finset (ι × ι)) (ψ φ : ι → ι → R) :
    car.tdaPairPauliDefect pairs₁ pairs₂ ψ φ • v = 0 := by
  dsimp [tdaPairPauliDefect]
  simp only [Finset.sum_smul, smul_assoc]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  rw [car.pairPauliDefect_smul_eq_zero v hvac, smul_zero]

omit [Algebra ℝ A] in
/-- Exact Quasiboson Approximation (QBA) recovery on any Fock vacuum state `v` for
oriented TDA pair operators. -/
theorem comm_tdaPair_smul_vacuum (v : V) (hvac : ∀ i, car.a i • v = 0)
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (ψ φ : ι → ι → R) :
    comm (car.tdaPairAnnihilation pairs ψ) (car.tdaPairCreation pairs φ) • v =
      (∑ p ∈ pairs, ψ p.1 p.2 * φ p.1 p.2) • v := by
  rw [car.comm_tdaPairAnnihilation_tdaPairCreation_oriented pairs h_no_swap,
    sub_smul, smul_assoc, one_smul, car.tdaPairPauliDefect_smul_eq_zero v hvac, sub_zero]

omit [Algebra ℝ A] in
/-- On a Fock vacuum state, orthonormal oriented TDA pairs satisfy the exact canonical
bosonic commutator eigenvalue `δ_{μμ'} • v`. -/
theorem comm_tdaPair_orthonormal_smul_vacuum
    {ι_ph : Type*} [DecidableEq ι_ph]
    (v : V) (hvac : ∀ i, car.a i • v = 0)
    (pairs : Finset (ι × ι))
    (h_no_swap : ∀ p ∈ pairs, (p.2, p.1) ∉ pairs)
    (ψ : ι_ph → ι → ι → R) (μ μ' : ι_ph)
    (h_ortho : ∑ p ∈ pairs, ψ μ p.1 p.2 * ψ μ' p.1 p.2 = if μ = μ' then (1 : R) else 0) :
    comm (car.tdaPairAnnihilation pairs (ψ μ)) (car.tdaPairCreation pairs (ψ μ')) • v =
      (if μ = μ' then (1 : R) else 0) • v := by
  rw [car.comm_tdaPair_smul_vacuum v hvac pairs h_no_swap, h_ortho]

end VacuumQBA

end TDALinearCombinations

omit [Algebra ℝ A] in
/-- **Okubo's Associative No-Go Theorem** (`PhysRevC.10.2045` Eqs. 1–2): in any nontrivial
associative CAR algebra with at least two distinct modes, imposing the one-fermion subspace
truncation `a_i * a_j = 0` for all `i, j` yields a contradiction. -/
theorem okubo_one_fermion_associative_obstruction [Nontrivial A]
    (h_two : ∃ i j : ι, i ≠ j)
    (h_one_fermion : ∀ i j, car.a i * car.a j = 0) : False := by
  rcases h_two with ⟨i, j, hij⟩
  have hjj : car.adag j * car.a j = 1 - car.a j * car.adag j := by
    have h := car.anticomm_a_adag j j
    simp only [↓reduceIte] at h
    exact eq_sub_of_add_eq' h
  have h1 : car.a i * (car.adag j * car.a j) = car.a i := by
    rw [hjj, mul_sub, mul_one, ← mul_assoc, h_one_fermion i j, zero_mul, sub_zero]
  have h2 : car.a i * (car.adag j * car.a j) = 0 := by
    rw [← mul_assoc, car.a_mul_adag_distinct i j hij, neg_mul, mul_assoc,
      h_one_fermion i j, mul_zero, neg_zero]
  have hai : car.a i = 0 := h1.symm.trans h2
  have hunit : (1 : A) = 0 := by
    have h := car.anticomm_a_adag i i
    simp only [↓reduceIte, hai, zero_mul, mul_zero, add_zero] at h
    exact h.symm
  exact one_ne_zero hunit

/-! ## Obstruction-Driven 5-Graded Lie Algebra (`totalNumberOp` Weights `±2, ±1, 0`) -/

section FiveGradeLieAlgebra

omit [Algebra ℝ A] in
/-- Leibniz derivation law for the associative commutator `comm Z (X * Y)`. -/
theorem comm_mul_right (Z X Y : A) :
    comm Z (X * Y) = comm Z X * Y + X * comm Z Y := by
  dsimp [comm]
  noncomm_ring

/-- Same-index number-annihilation commutator `[N_k, α_k] = - α_k`. -/
theorem comm_numberOp_a_same_ring (k : ι) :
    comm (car.numberOp k) (car.a k) = -car.a k := by
  dsimp [comm, numberOp]
  calc car.adag k * car.a k * car.a k - car.a k * (car.adag k * car.a k)
      = car.adag k * (car.a k * car.a k) - (car.a k * car.adag k) * car.a k := by
        noncomm_ring
    _ = car.adag k * 0 - (1 - car.adag k * car.a k) * car.a k := by
        rw [car.a_sq k, car.a_mul_adag_same k]
    _ = -car.a k + (car.adag k * car.a k) * car.a k := by
        rw [sub_mul, one_mul, mul_zero, zero_sub]
        abel_nf
    _ = -car.a k := by
        rw [mul_assoc, car.a_sq k, mul_zero, add_zero]

omit [Algebra ℝ A] in
/-- Total quasiparticle number operator on any finite mode support `s : Finset ι`. -/
def totalNumberOp (s : Finset ι) : A :=
  ∑ i ∈ s, car.numberOp i

omit [Algebra ℝ A] in
/-- Linearity of `comm (car.totalNumberOp s)` across finite sums. -/
theorem comm_totalNumberOp_sum {β : Type*} (t : Finset β) (f : β → A) (s : Finset ι) :
    comm (car.totalNumberOp s) (∑ x ∈ t, f x) =
      ∑ x ∈ t, comm (car.totalNumberOp s) (f x) := by
  dsimp [comm]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- Grade `+1`: `[N_s, α_k†] = α_k†` for every `k ∈ s`. -/
theorem comm_totalNumberOp_adag (s : Finset ι) (k : ι) (hk : k ∈ s) :
    comm (car.totalNumberOp s) (car.adag k) = car.adag k := by
  dsimp [totalNumberOp, comm]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · exact car.comm_numberOp_adag_same k
  · intro j _ hjk
    exact car.comm_numberOp_adag_distinct j k hjk
  · intro hnk
    exact False.elim (hnk hk)

/-- Grade `-1`: `[N_s, α_k] = -α_k` for every `k ∈ s`. -/
theorem comm_totalNumberOp_a (s : Finset ι) (k : ι) (hk : k ∈ s) :
    comm (car.totalNumberOp s) (car.a k) = -car.a k := by
  dsimp [totalNumberOp, comm]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · exact car.comm_numberOp_a_same_ring k
  · intro j _ hjk
    exact car.comm_numberOp_a_distinct_carrier j k hjk
  · intro hnk
    exact False.elim (hnk hk)

/-- Grade `0`: `[N_s, α_i† α_j] = 0` for all `i, j ∈ s` (scattering sector). -/
theorem comm_totalNumberOp_scattering (s : Finset ι) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    comm (car.totalNumberOp s) (car.adag i * car.a j) = 0 := by
  rw [comm_mul_right, car.comm_totalNumberOp_adag s i hi,
    car.comm_totalNumberOp_a s j hj, mul_neg, add_neg_cancel]

/-- Grade `+2`: `[N_s, B_{ab}†] = 2 • B_{ab}† = B_{ab}† + B_{ab}†` for `a, b ∈ s`. -/
theorem comm_totalNumberOp_pairCreation (s : Finset ι) {a b : ι} (ha : a ∈ s) (hb : b ∈ s) :
    comm (car.totalNumberOp s) (car.pairCreation a b) =
      car.pairCreation a b + car.pairCreation a b := by
  dsimp [pairCreation]
  rw [comm_mul_right, car.comm_totalNumberOp_adag s a ha,
    car.comm_totalNumberOp_adag s b hb]

/-- Grade `-2`: `[N_s, B_{ab}] = -(B_{ab} + B_{ab})` for `a, b ∈ s`. -/
theorem comm_totalNumberOp_pairAnnihilation (s : Finset ι) {a b : ι} (ha : a ∈ s) (hb : b ∈ s) :
    comm (car.totalNumberOp s) (car.pairAnnihilation a b) =
      -(car.pairAnnihilation a b + car.pairAnnihilation a b) := by
  dsimp [pairAnnihilation]
  rw [comm_mul_right, car.comm_totalNumberOp_a s b hb,
    car.comm_totalNumberOp_a s a ha]
  noncomm_ring

/-- Grade `0` on the Pauli-blocking defect: `[N_s, pairPauliDefect a b c d] = 0`. -/
theorem comm_totalNumberOp_pairPauliDefect (s : Finset ι) {a b c d : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) :
    comm (car.totalNumberOp s) (car.pairPauliDefect a b c d) = 0 := by
  dsimp [pairPauliDefect]
  have hsub (X Y : A) :
      comm (car.totalNumberOp s) (X - Y) =
        comm (car.totalNumberOp s) X - comm (car.totalNumberOp s) Y := by
    dsimp [comm]; noncomm_ring
  have hadd (X Y : A) :
      comm (car.totalNumberOp s) (X + Y) =
        comm (car.totalNumberOp s) X + comm (car.totalNumberOp s) Y := by
    dsimp [comm]; noncomm_ring
  have hzero : comm (car.totalNumberOp s) (0 : A) = 0 := by
    dsimp [comm]; simp
  rw [hadd, hsub, hsub]
  have hdb := car.comm_totalNumberOp_scattering s hd hb
  have hda := car.comm_totalNumberOp_scattering s hd ha
  have hcb := car.comm_totalNumberOp_scattering s hc hb
  have hca := car.comm_totalNumberOp_scattering s hc ha
  split_ifs <;> simp only [hdb, hda, hcb, hca, hzero, sub_self, add_zero]

/-- `[grade -2, grade +2] → grade 0`: the pair commutator `[B_{ab}, B_{cd}†]` always has
total number weight `0`. -/
theorem comm_totalNumberOp_comm_pair_eq_zero (s : Finset ι) {a b c d : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) :
    comm (car.totalNumberOp s) (comm (car.pairAnnihilation a b) (car.pairCreation c d)) = 0 := by
  rw [car.comm_pairAnnihilation_pairCreation]
  have hsub (X Y : A) :
      comm (car.totalNumberOp s) (X - Y) =
        comm (car.totalNumberOp s) X - comm (car.totalNumberOp s) Y := by
    dsimp [comm]; noncomm_ring
  rw [hsub, car.comm_totalNumberOp_pairPauliDefect s ha hb hc hd, sub_zero]
  dsimp [comm]
  split_ifs <;> simp

/-- Collective TDA pair creation lies in grade `+2` under `totalNumberOp s`. -/
theorem comm_totalNumberOp_tdaPairCreation {R : Type*} [CommRing R] [Algebra R A]
    (s : Finset ι)
    (pairs : Finset (ι × ι)) (hs : ∀ p ∈ pairs, p.1 ∈ s ∧ p.2 ∈ s)
    (ψ : ι → ι → R) :
    comm (car.totalNumberOp s) (car.tdaPairCreation pairs ψ) =
      car.tdaPairCreation pairs ψ + car.tdaPairCreation pairs ψ := by
  dsimp [tdaPairCreation]
  rw [car.comm_totalNumberOp_sum]
  calc
    ∑ p ∈ pairs, comm (car.totalNumberOp s) (ψ p.1 p.2 • car.pairCreation p.1 p.2)
      = ∑ p ∈ pairs, ψ p.1 p.2 • comm (car.totalNumberOp s) (car.pairCreation p.1 p.2) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          dsimp [comm]
          rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
    _ = ∑ p ∈ pairs, ψ p.1 p.2 • (car.pairCreation p.1 p.2 + car.pairCreation p.1 p.2) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [car.comm_totalNumberOp_pairCreation s (hs p hp).1 (hs p hp).2]
    _ = (∑ p ∈ pairs, ψ p.1 p.2 • car.pairCreation p.1 p.2) +
          (∑ p ∈ pairs, ψ p.1 p.2 • car.pairCreation p.1 p.2) := by
          simp only [smul_add, Finset.sum_add_distrib]

/-- Collective TDA pair annihilation lies in grade `-2` under `totalNumberOp s`. -/
theorem comm_totalNumberOp_tdaPairAnnihilation {R : Type*} [CommRing R] [Algebra R A]
    (s : Finset ι)
    (pairs : Finset (ι × ι)) (hs : ∀ p ∈ pairs, p.1 ∈ s ∧ p.2 ∈ s)
    (ψ : ι → ι → R) :
    comm (car.totalNumberOp s) (car.tdaPairAnnihilation pairs ψ) =
      -(car.tdaPairAnnihilation pairs ψ + car.tdaPairAnnihilation pairs ψ) := by
  dsimp [tdaPairAnnihilation]
  rw [car.comm_totalNumberOp_sum]
  calc
    ∑ p ∈ pairs, comm (car.totalNumberOp s) (ψ p.1 p.2 • car.pairAnnihilation p.1 p.2)
      = ∑ p ∈ pairs, ψ p.1 p.2 • comm (car.totalNumberOp s) (car.pairAnnihilation p.1 p.2) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          dsimp [comm]
          rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
    _ = ∑ p ∈ pairs,
          ψ p.1 p.2 • (-(car.pairAnnihilation p.1 p.2 + car.pairAnnihilation p.1 p.2)) := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [car.comm_totalNumberOp_pairAnnihilation s (hs p hp).1 (hs p hp).2]
    _ = -((∑ p ∈ pairs, ψ p.1 p.2 • car.pairAnnihilation p.1 p.2) +
          (∑ p ∈ pairs, ψ p.1 p.2 • car.pairAnnihilation p.1 p.2)) := by
          simp only [smul_neg, smul_add, Finset.sum_neg_distrib, Finset.sum_add_distrib]

/-- Collective TDA Pauli-blocking defect lies in grade `0` under `totalNumberOp s`. -/
theorem comm_totalNumberOp_tdaPairPauliDefect {R : Type*} [CommRing R] [Algebra R A]
    (s : Finset ι)
    (pairs₁ pairs₂ : Finset (ι × ι))
    (hs₁ : ∀ p ∈ pairs₁, p.1 ∈ s ∧ p.2 ∈ s)
    (hs₂ : ∀ q ∈ pairs₂, q.1 ∈ s ∧ q.2 ∈ s)
    (ψ φ : ι → ι → R) :
    comm (car.totalNumberOp s) (car.tdaPairPauliDefect pairs₁ pairs₂ ψ φ) = 0 := by
  dsimp [tdaPairPauliDefect]
  rw [car.comm_totalNumberOp_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [car.comm_totalNumberOp_sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hsmul :
      comm (car.totalNumberOp s)
          ((ψ p.1 p.2 * φ q.1 q.2) • car.pairPauliDefect p.1 p.2 q.1 q.2) =
        (ψ p.1 p.2 * φ q.1 q.2) •
          comm (car.totalNumberOp s) (car.pairPauliDefect p.1 p.2 q.1 q.2) := by
    dsimp [comm]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  rw [hsmul, car.comm_totalNumberOp_pairPauliDefect s
    (hs₁ p hp).1 (hs₁ p hp).2 (hs₂ q hq).1 (hs₂ q hq).2, smul_zero]

omit [Algebra ℝ A] in
/-- `[grade 0, grade +2] → grade +2`: the scattering sector closes onto pair creation. -/
theorem comm_scattering_pairCreation (i j c d : ι) :
    comm (car.adag i * car.a j) (car.pairCreation c d) =
      (if j = c then car.pairCreation i d else 0) -
        (if j = d then car.pairCreation i c else 0) := by
  dsimp [comm, pairCreation]
  have h1 : car.a j * car.adag c = (if j = c then (1 : A) else 0) - car.adag c * car.a j :=
    eq_sub_of_add_eq (car.anticomm_a_adag j c)
  have h2 : car.a j * car.adag d = (if j = d then (1 : A) else 0) - car.adag d * car.a j :=
    eq_sub_of_add_eq (car.anticomm_a_adag j d)
  have h_ic : car.adag c * car.adag i = -(car.adag i * car.adag c) :=
    car.adag_mul_adag_comm i c
  have h_id : car.adag d * car.adag i = -(car.adag i * car.adag d) :=
    car.adag_mul_adag_comm i d
  calc
    (car.adag i * car.a j) * (car.adag c * car.adag d) -
        (car.adag c * car.adag d) * (car.adag i * car.a j)
      = car.adag i * ((car.a j * car.adag c) * car.adag d) -
          (car.adag c * (car.adag d * car.adag i)) * car.a j := by noncomm_ring
    _ = car.adag i * (((if j = c then (1 : A) else 0) - car.adag c * car.a j) * car.adag d) -
          (car.adag c * (-(car.adag i * car.adag d))) * car.a j := by
        rw [h1, h_id]
    _ = (if j = c then car.adag i * car.adag d else 0) -
          car.adag i * (car.adag c * (car.a j * car.adag d)) +
          ((car.adag c * car.adag i) * car.adag d) * car.a j := by
        split_ifs <;> noncomm_ring
    _ = (if j = c then car.adag i * car.adag d else 0) -
          car.adag i * (car.adag c * ((if j = d then (1 : A) else 0) - car.adag d * car.a j)) +
          ((-(car.adag i * car.adag c)) * car.adag d) * car.a j := by
        rw [h2, h_ic]
    _ = (if j = c then car.adag i * car.adag d else 0) -
          (if j = d then car.adag i * car.adag c else 0) := by
        split_ifs <;> noncomm_ring

omit [Algebra ℝ A] in
/-- `[grade -2, grade 0] → grade -2`: pair annihilation commutes with scattering back into
pair annihilation. -/
theorem comm_pairAnnihilation_scattering (a b i j : ι) :
    comm (car.pairAnnihilation a b) (car.adag i * car.a j) =
      (if a = i then car.pairAnnihilation j b else 0) -
        (if b = i then car.pairAnnihilation j a else 0) := by
  dsimp [comm, pairAnnihilation]
  have h1 : car.a a * car.adag i = (if a = i then (1 : A) else 0) - car.adag i * car.a a :=
    eq_sub_of_add_eq (car.anticomm_a_adag a i)
  have h2 : car.a b * car.adag i = (if b = i then (1 : A) else 0) - car.adag i * car.a b :=
    eq_sub_of_add_eq (car.anticomm_a_adag b i)
  have h_ja : car.a j * car.a a = -(car.a a * car.a j) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_a_a j a)
  have h_jb : car.a j * car.a b = -(car.a b * car.a j) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_a_a j b)
  calc
    (car.a b * car.a a) * (car.adag i * car.a j) -
        (car.adag i * car.a j) * (car.a b * car.a a)
      = (car.a b * (car.a a * car.adag i)) * car.a j -
          car.adag i * ((car.a j * car.a b) * car.a a) := by noncomm_ring
    _ = (car.a b * ((if a = i then (1 : A) else 0) - car.adag i * car.a a)) * car.a j -
          car.adag i * ((-(car.a b * car.a j)) * car.a a) := by
        rw [h1, h_jb]
    _ = (if a = i then car.a b * car.a j else 0) -
          ((car.a b * car.adag i) * car.a a) * car.a j +
          car.adag i * (car.a b * (car.a j * car.a a)) := by
        split_ifs <;> noncomm_ring
    _ = (if a = i then car.a b * car.a j else 0) -
          (((if b = i then (1 : A) else 0) - car.adag i * car.a b) * car.a a) * car.a j +
          car.adag i * (car.a b * (-(car.a a * car.a j))) := by
        rw [h2, h_ja]
    _ = (if a = i then car.a b * car.a j else 0) -
          (if b = i then car.a a * car.a j else 0) := by
        split_ifs <;> noncomm_ring

omit [Algebra ℝ A] in
/-- `[grade 0, grade 0] → grade 0`: scattering operators form a closed `gl(ι)` subalgebra. -/
theorem comm_scattering_scattering (i j k l : ι) :
    comm (car.adag i * car.a j) (car.adag k * car.a l) =
      (if j = k then car.adag i * car.a l else 0) -
        (if i = l then car.adag k * car.a j else 0) := by
  dsimp [comm]
  have h1 : car.a j * car.adag k = (if j = k then (1 : A) else 0) - car.adag k * car.a j :=
    eq_sub_of_add_eq (car.anticomm_a_adag j k)
  have h2 : car.a l * car.adag i = (if i = l then (1 : A) else 0) - car.adag i * car.a l := by
    have h := car.anticomm_a_adag l i
    rw [eq_comm] at h
    exact eq_sub_of_add_eq (car.anticomm_a_adag l i) |>.trans (by congr 1; simp [eq_comm])
  have h_ik : car.adag i * car.adag k = -(car.adag k * car.adag i) :=
    car.adag_mul_adag_comm k i
  have h_jl : car.a j * car.a l = -(car.a l * car.a j) :=
    eq_neg_of_add_eq_zero_left (car.anticomm_a_a j l)
  calc
    (car.adag i * car.a j) * (car.adag k * car.a l) -
        (car.adag k * car.a l) * (car.adag i * car.a j)
      = car.adag i * (car.a j * car.adag k) * car.a l -
          car.adag k * (car.a l * car.adag i) * car.a j := by noncomm_ring
    _ = car.adag i * ((if j = k then (1 : A) else 0) - car.adag k * car.a j) * car.a l -
          car.adag k * ((if i = l then (1 : A) else 0) - car.adag i * car.a l) * car.a j := by
        rw [h1, h2]
    _ = (if j = k then car.adag i * car.a l else 0) -
          (if i = l then car.adag k * car.a j else 0) -
          ((car.adag i * car.adag k) * (car.a j * car.a l) -
            car.adag k * car.adag i * (car.a l * car.a j)) := by
        split_ifs <;> noncomm_ring
    _ = (if j = k then car.adag i * car.a l else 0) -
          (if i = l then car.adag k * car.a j else 0) -
          ((-(car.adag k * car.adag i)) * (-(car.a l * car.a j)) -
            car.adag k * car.adag i * (car.a l * car.a j)) := by
        rw [h_ik, h_jl]
    _ = (if j = k then car.adag i * car.a l else 0) -
          (if i = l then car.adag k * car.a j else 0) := by
        noncomm_ring

/-- Exact 5-grade weight action of `totalNumberOp s` on an arbitrary `ℝ`-linear combination of
grades `+2, +1, 0, -1, -2`. -/
theorem comm_totalNumberOp_fiveGrade_linear (s : Finset ι) {a b c d i j k l : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (hl : l ∈ s)
    (c2 c1 c0 cm1 cm2 : ℝ) :
    comm (car.totalNumberOp s)
        (c2 • car.pairCreation c d + c1 • car.adag k + c0 • (car.adag i * car.a j) +
          cm1 • car.a l + cm2 • car.pairAnnihilation a b) =
      (2 * c2) • car.pairCreation c d + c1 • car.adag k -
        cm1 • car.a l - (2 * cm2) • car.pairAnnihilation a b := by
  have hadd : ∀ U W : A,
      comm (car.totalNumberOp s) (U + W) =
        comm (car.totalNumberOp s) U + comm (car.totalNumberOp s) W := by
    intro U W; dsimp [comm]; noncomm_ring
  have hsmul : ∀ (r : ℝ) (U : A),
      comm (car.totalNumberOp s) (r • U) = r • comm (car.totalNumberOp s) U := by
    intro r U; dsimp [comm]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  rw [hadd, hadd, hadd, hadd, hsmul, hsmul, hsmul, hsmul, hsmul]
  rw [car.comm_totalNumberOp_pairCreation s hc hd,
    car.comm_totalNumberOp_adag s k hk,
    car.comm_totalNumberOp_scattering s hi hj,
    car.comm_totalNumberOp_a s l hl,
    car.comm_totalNumberOp_pairAnnihilation s ha hb]
  rw [smul_zero, add_zero, smul_neg, smul_neg, ← two_smul_real, ← two_smul_real]
  rw [smul_smul, smul_smul, mul_comm c2 2, mul_comm cm2 2]
  abel

end FiveGradeLieAlgebra

/-- Microscopic forward RPA/TDA relation: the single-mode quasiparticle number
operator raises a pair creation by one for each coincident index.  This is the
fermionic origin of the collective TDA forward commutator algebra. -/
theorem comm_numberOp_pairCreation (k a b : ι) :
    comm (car.numberOp k) (car.pairCreation a b) =
      ((if k = a then (1 : A) else 0) + (if k = b then (1 : A) else 0)) *
        car.pairCreation a b := by
  dsimp [pairCreation]
  rw [comm_mul_right]
  have h1 : comm (car.numberOp k) (car.adag a) = if k = a then car.adag a else 0 := by
    by_cases h : k = a
    · rw [h, car.comm_numberOp_adag_same a]
      simp
    · rw [car.comm_numberOp_adag_distinct k a h]
      simp [h]
  have h2 : comm (car.numberOp k) (car.adag b) = if k = b then car.adag b else 0 := by
    by_cases h : k = b
    · rw [h, car.comm_numberOp_adag_same b]
      simp
    · rw [car.comm_numberOp_adag_distinct k b h]
      simp [h]
  rw [h1, h2]
  split_ifs <;> noncomm_ring

/-- Dual microscopic relation: each coincident index lowers a pair annihilation. -/
theorem comm_numberOp_pairAnnihilation (k a b : ι) :
    comm (car.numberOp k) (car.pairAnnihilation a b) =
      -(((if k = a then (1 : A) else 0) + (if k = b then (1 : A) else 0)) *
        car.pairAnnihilation a b) := by
  dsimp [pairAnnihilation]
  rw [comm_mul_right]
  have h1 : comm (car.numberOp k) (car.a b) = if k = b then -car.a b else 0 := by
    by_cases h : k = b
    · rw [h, car.comm_numberOp_a_same_ring b]
      simp
    · rw [car.comm_numberOp_a_distinct_carrier k b h]
      simp [h]
  have h2 : comm (car.numberOp k) (car.a a) = if k = a then -car.a a else 0 := by
    by_cases h : k = a
    · rw [h, car.comm_numberOp_a_same_ring a]
      simp
    · rw [car.comm_numberOp_a_distinct_carrier k a h]
      simp [h]
  rw [h1, h2]
  split_ifs <;> noncomm_ring

variable {R : Type*} [CommRing R] [Algebra R A]

omit [Algebra ℝ A] in
/-- Commutator of a fixed operator with an `R`-weighted finite sum. -/
private theorem comm_single_sum_smul {β : Type*} (Z : A) (s : Finset β)
    (d : β → R) (Y : β → A) :
    comm Z (∑ q ∈ s, d q • Y q) = ∑ q ∈ s, d q • comm Z (Y q) := by
  dsimp [comm]
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  rw [← Finset.sum_sub_distrib]

/-- Collective forward TDA relation: the microscopic number-pair commutator
sums to the number commutator with the whole collective creation phonon. -/
theorem comm_numberOp_tdaPairCreation (k : ι) (pairs : Finset (ι × ι)) (ψ : ι → ι → R) :
    comm (car.numberOp k) (car.tdaPairCreation pairs ψ) =
      ∑ p ∈ pairs, ψ p.1 p.2 •
        (((if k = p.1 then (1 : A) else 0) + (if k = p.2 then (1 : A) else 0)) *
          car.pairCreation p.1 p.2) := by
  dsimp [tdaPairCreation]
  rw [comm_single_sum_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [QuasiparticleCAR.comm_numberOp_pairCreation (car := car) k p.1 p.2]

/-- Dual collective relation for the TDA annihilation phonon. -/
theorem comm_numberOp_tdaPairAnnihilation (k : ι) (pairs : Finset (ι × ι)) (ψ : ι → ι → R) :
    comm (car.numberOp k) (car.tdaPairAnnihilation pairs ψ) =
      ∑ p ∈ pairs, ψ p.1 p.2 •
        (-(((if k = p.1 then (1 : A) else 0) + (if k = p.2 then (1 : A) else 0)) *
          car.pairAnnihilation p.1 p.2)) := by
  dsimp [tdaPairAnnihilation]
  rw [comm_single_sum_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [QuasiparticleCAR.comm_numberOp_pairAnnihilation (car := car) k p.1 p.2]

end QuasiparticleCAR

/-- Concrete single-mode `2 × 2` real Pauli-matrix witness inhabiting `QuasiparticleCAR`
(`T17` non-vacuity). -/
def pauliCARWitness : QuasiparticleCAR Unit (Matrix (Fin 2) (Fin 2) ℝ) where
  a _ := !![0, 1; 0, 0]
  adag _ := !![0, 0; 1, 0]
  anticomm_a_a _ _ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  anticomm_adag_adag _ _ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  anticomm_a_adag _ _ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp

end InfoGeometry.Physics.NuclearQuasiparticleCAR
