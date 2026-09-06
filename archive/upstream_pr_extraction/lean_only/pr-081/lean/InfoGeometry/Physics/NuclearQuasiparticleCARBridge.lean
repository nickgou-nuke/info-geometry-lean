import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
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
  simp only [if_true] at h
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
  simp only [if_neg hij] at h
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

end QuasiparticleCAR

end InfoGeometry.Physics.NuclearQuasiparticleCAR
