import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge

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
    simp only [if_true, comm] at h
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
    simp only [if_neg hij, comm] at h
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

end PhononRPA

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

end InfoGeometry.Physics.NuclearPhononRPA
