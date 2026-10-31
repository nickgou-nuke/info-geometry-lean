/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearPhononRPAAlgebra

/-!
# Phonon Hamiltonians with operator coefficients

The mode coefficients belong to the same arbitrary operator ring as the
creation, annihilation, and number operators. Their commutators are retained
in the exact evolution law. No coefficient is required to be central.
-/

namespace InfoGeometry.Physics.NuclearPhononRPA.PhononRPA

open scoped BigOperators

variable {ι A : Type*} [DecidableEq ι] [Ring A]

/-- The ordered mode sum with coefficients in the operator ring. -/
def operatorWeightedHamiltonian (rpa : PhononRPA ι A)
    (s : Finset ι) (Ω : ι → A) : A :=
  ∑ i ∈ s, Ω i * rpa.numberOp i

/-- Every coefficient commutator remains in the full operator evolution law. -/
theorem comm_operatorWeightedHamiltonian
    (rpa : PhononRPA ι A) (s : Finset ι) (Ω : ι → A) (X : A) :
    comm (rpa.operatorWeightedHamiltonian s Ω) X =
      ∑ i ∈ s, (Ω i * comm (rpa.numberOp i) X +
        comm (Ω i) X * rpa.numberOp i) := by
  simp only [operatorWeightedHamiltonian, comm, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  noncomm_ring

/-- Creation has its mode term and the exact noncentral coefficient correction. -/
theorem comm_operatorWeightedHamiltonian_Qdag
    (rpa : PhononRPA ι A) (s : Finset ι) (Ω : ι → A)
    (k : ι) (hk : k ∈ s) :
    comm (rpa.operatorWeightedHamiltonian s Ω) (rpa.Qdag k) =
      Ω k * rpa.Qdag k +
        ∑ i ∈ s, comm (Ω i) (rpa.Qdag k) * rpa.numberOp i := by
  rw [comm_operatorWeightedHamiltonian, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single k]
  · rw [rpa.comm_numberOp_Qdag_same]
  · intro i _ hik
    rw [rpa.comm_numberOp_Qdag_distinct i k hik, mul_zero]
  · intro hks
    exact False.elim (hks hk)

/-- If the number operators commute with an observable, all its evolution
comes from the operator coefficients. -/
theorem comm_operatorWeightedHamiltonian_of_number_commute
    (rpa : PhononRPA ι A) (s : Finset ι) (Ω : ι → A) (X : A)
    (hX : ∀ i ∈ s, Commute (rpa.numberOp i) X) :
    comm (rpa.operatorWeightedHamiltonian s Ω) X =
      ∑ i ∈ s, comm (Ω i) X * rpa.numberOp i := by
  rw [comm_operatorWeightedHamiltonian]
  apply Finset.sum_congr rfl
  intro i hi
  have hzero : comm (rpa.numberOp i) X = 0 := sub_eq_zero.mpr (hX i hi).eq
  rw [hzero, mul_zero, zero_add]

/-- Exact conservation criterion, allowing cancellation among coefficient
commutators rather than requiring every coefficient to commute separately. -/
theorem operatorWeightedHamiltonian_commute_iff
    (rpa : PhononRPA ι A) (s : Finset ι) (Ω : ι → A) (X : A)
    (hX : ∀ i ∈ s, Commute (rpa.numberOp i) X) :
    Commute (rpa.operatorWeightedHamiltonian s Ω) X ↔
      (∑ i ∈ s, comm (Ω i) X * rpa.numberOp i) = 0 := by
  constructor
  · intro h
    have hz : comm (rpa.operatorWeightedHamiltonian s Ω) X = 0 :=
      sub_eq_zero.mpr h.eq
    rwa [comm_operatorWeightedHamiltonian_of_number_commute rpa s Ω X hX] at hz
  · intro h
    show rpa.operatorWeightedHamiltonian s Ω * X = X * rpa.operatorWeightedHamiltonian s Ω
    apply sub_eq_zero.mp
    change comm (rpa.operatorWeightedHamiltonian s Ω) X = 0
    rw [comm_operatorWeightedHamiltonian_of_number_commute rpa s Ω X hX, h]

end InfoGeometry.Physics.NuclearPhononRPA.PhononRPA
