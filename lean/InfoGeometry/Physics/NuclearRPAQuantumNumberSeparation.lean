/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.NuclearPhononRPAAlgebra

/-!
# Nuclear CAR/RPA quantum-number separation

The existing coupled quasiparticle-phonon owner assumes independent CAR and RPA
operators commute across sectors.  This file derives the corresponding
consequences for the newly exposed quasiparticle Cartan, occupation projectors,
and fermion parity.

Thus, before an explicit interaction is introduced, quasiparticle occupation
and parity are compatible commuting quantum numbers with the phonon-number
sector.  No statement is made that an interacting nuclear Hamiltonian must
preserve these labels.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearRPAQuantumNumberSeparation

open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearCartanProjectorParityBridge
open InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR
open InfoGeometry.Physics.NuclearPhononRPA

variable {ι_qp ι_ph : Type*}
variable [DecidableEq ι_qp] [DecidableEq ι_ph]
variable {A : Type*} [Ring A] [Algebra ℝ A]

variable (sys : CoupledQuasiparticlePhononSystem ι_qp ι_ph A)

private theorem commute_of_comm_eq_zero {X Y : A}
    (h : NuclearPhononRPA.comm X Y = 0) : X * Y = Y * X := by
  exact sub_eq_zero.mp h

/-- The quasiparticle occupation operator commutes with phonon annihilation. -/
theorem numberOp_comm_Q (i : ι_qp) (j : ι_ph) :
    NuclearPhononRPA.comm (sys.car.numberOp i) (sys.rpa.Q j) = 0 := by
  have ha := commute_of_comm_eq_zero (sys.cross_comm_a_Q i j)
  have hadag := commute_of_comm_eq_zero (sys.cross_comm_adag_Q i j)
  unfold NuclearPhononRPA.comm NuclearQuasiparticleCAR.QuasiparticleCAR.numberOp
  rw [show sys.car.adag i * sys.car.a i * sys.rpa.Q j =
      sys.rpa.Q j * (sys.car.adag i * sys.car.a i) by
    calc
      sys.car.adag i * sys.car.a i * sys.rpa.Q j =
          sys.car.adag i * (sys.car.a i * sys.rpa.Q j) := by simp [mul_assoc]
      _ = sys.car.adag i * (sys.rpa.Q j * sys.car.a i) := by rw [ha]
      _ = (sys.car.adag i * sys.rpa.Q j) * sys.car.a i := by simp [mul_assoc]
      _ = (sys.rpa.Q j * sys.car.adag i) * sys.car.a i := by rw [hadag]
      _ = sys.rpa.Q j * (sys.car.adag i * sys.car.a i) := by simp [mul_assoc]]
  exact sub_self _

/-- The quasiparticle occupation operator commutes with phonon creation. -/
theorem numberOp_comm_Qdag (i : ι_qp) (j : ι_ph) :
    NuclearPhononRPA.comm (sys.car.numberOp i) (sys.rpa.Qdag j) = 0 := by
  have ha := commute_of_comm_eq_zero (sys.cross_comm_a_Qdag i j)
  have hadag := commute_of_comm_eq_zero (sys.cross_comm_adag_Qdag i j)
  unfold NuclearPhononRPA.comm NuclearQuasiparticleCAR.QuasiparticleCAR.numberOp
  rw [show sys.car.adag i * sys.car.a i * sys.rpa.Qdag j =
      sys.rpa.Qdag j * (sys.car.adag i * sys.car.a i) by
    calc
      sys.car.adag i * sys.car.a i * sys.rpa.Qdag j =
          sys.car.adag i * (sys.car.a i * sys.rpa.Qdag j) := by simp [mul_assoc]
      _ = sys.car.adag i * (sys.rpa.Qdag j * sys.car.a i) := by rw [ha]
      _ = (sys.car.adag i * sys.rpa.Qdag j) * sys.car.a i := by simp [mul_assoc]
      _ = (sys.rpa.Qdag j * sys.car.adag i) * sys.car.a i := by rw [hadag]
      _ = sys.rpa.Qdag j * (sys.car.adag i * sys.car.a i) := by simp [mul_assoc]]
  exact sub_self _

/-- Quasiparticle and phonon number operators commute. -/
theorem numberOp_comm_phononNumberOp (i : ι_qp) (j : ι_ph) :
    NuclearPhononRPA.comm (sys.car.numberOp i) (sys.rpa.numberOp j) = 0 := by
  have hQ := commute_of_comm_eq_zero (numberOp_comm_Q sys i j)
  have hQdag := commute_of_comm_eq_zero (numberOp_comm_Qdag sys i j)
  unfold NuclearPhononRPA.comm NuclearPhononRPA.PhononRPA.numberOp
  rw [show sys.car.numberOp i * (sys.rpa.Qdag j * sys.rpa.Q j) =
      (sys.rpa.Qdag j * sys.rpa.Q j) * sys.car.numberOp i by
    calc
      sys.car.numberOp i * (sys.rpa.Qdag j * sys.rpa.Q j) =
          (sys.car.numberOp i * sys.rpa.Qdag j) * sys.rpa.Q j := by simp [mul_assoc]
      _ = (sys.rpa.Qdag j * sys.car.numberOp i) * sys.rpa.Q j := by rw [hQdag]
      _ = sys.rpa.Qdag j * (sys.car.numberOp i * sys.rpa.Q j) := by simp [mul_assoc]
      _ = sys.rpa.Qdag j * (sys.rpa.Q j * sys.car.numberOp i) := by rw [hQ]
      _ = (sys.rpa.Qdag j * sys.rpa.Q j) * sys.car.numberOp i := by simp [mul_assoc]]
  exact sub_self _

/-- The centered quasiparticle Cartan commutes with phonon number. -/
theorem centeredCartan_comm_phononNumberOp (i : ι_qp) (j : ι_ph) :
    NuclearPhononRPA.comm (sys.car.centeredOccupationCartan i)
      (sys.rpa.numberOp j) = 0 := by
  have hN := numberOp_comm_phononNumberOp sys i j
  unfold NuclearPhononRPA.comm centeredOccupationCartan at *
  have hcomm : sys.car.numberOp i * sys.rpa.numberOp j =
      sys.rpa.numberOp j * sys.car.numberOp i := sub_eq_zero.mp hN
  noncomm_ring [hcomm]

/-- The vacancy projector commutes with phonon number. -/
theorem vacancyProjector_comm_phononNumberOp (i : ι_qp) (j : ι_ph) :
    NuclearPhononRPA.comm (sys.car.vacancyProjector i)
      (sys.rpa.numberOp j) = 0 := by
  have hN := numberOp_comm_phononNumberOp sys i j
  unfold NuclearPhononRPA.comm vacancyProjector at *
  have hcomm : sys.car.numberOp i * sys.rpa.numberOp j =
      sys.rpa.numberOp j * sys.car.numberOp i := sub_eq_zero.mp hN
  noncomm_ring [hcomm]

/-- One-mode quasiparticle fermion parity commutes with phonon number. -/
theorem fermionParity_comm_phononNumberOp (i : ι_qp) (j : ι_ph) :
    NuclearPhononRPA.comm (sys.car.fermionParity i)
      (sys.rpa.numberOp j) = 0 := by
  have hN := numberOp_comm_phononNumberOp sys i j
  unfold NuclearPhononRPA.comm fermionParity at *
  have hcomm : sys.car.numberOp i * sys.rpa.numberOp j =
      sys.rpa.numberOp j * sys.car.numberOp i := sub_eq_zero.mp hN
  noncomm_ring [hcomm]

/-- Closed commuting-quantum-number packet for an independent CAR/RPA pair. -/
theorem car_rpa_quantum_number_separation_packet (i : ι_qp) (j : ι_ph) :
    NuclearPhononRPA.comm (sys.car.numberOp i) (sys.rpa.numberOp j) = 0 ∧
      NuclearPhononRPA.comm (sys.car.centeredOccupationCartan i)
        (sys.rpa.numberOp j) = 0 ∧
      NuclearPhononRPA.comm (sys.car.vacancyProjector i)
        (sys.rpa.numberOp j) = 0 ∧
      NuclearPhononRPA.comm (sys.car.fermionParity i)
        (sys.rpa.numberOp j) = 0 :=
  ⟨numberOp_comm_phononNumberOp sys i j,
    centeredCartan_comm_phononNumberOp sys i j,
    vacancyProjector_comm_phononNumberOp sys i j,
    fermionParity_comm_phononNumberOp sys i j⟩

/-! ## Pair-Number (`ΔN = ±2`) and Neutral Scattering (`ΔN = 0`) Quantum-Number Separation -/

section PairNumberAndScattering

/-- Total quasiparticle number operator `N = ∑ i ∈ s, car.numberOp i` on a finite orbital set `s`. -/
def totalNumberOp (car : QuasiparticleCAR ι_qp A) (s : Finset ι_qp) : A :=
  ∑ i ∈ s, car.numberOp i

private theorem comm_numberOp_adag_ite (car : QuasiparticleCAR ι_qp A) (i j : ι_qp) :
    NuclearPhononRPA.comm (car.numberOp i) (car.adag j) =
      (if i = j then (1 : ℝ) else 0) • car.adag j := by
  by_cases hij : i = j
  · subst hij
    simpa [NuclearPhononRPA.comm, QuasiparticleCAR.comm] using car.comm_numberOp_adag_same i
  · simpa [NuclearPhononRPA.comm, QuasiparticleCAR.comm, hij] using
      car.comm_numberOp_adag_distinct i j hij

private theorem comm_numberOp_a_ite (car : QuasiparticleCAR ι_qp A) (i j : ι_qp) :
    NuclearPhononRPA.comm (car.numberOp i) (car.a j) =
      -((if i = j then (1 : ℝ) else 0) • car.a j) := by
  by_cases hij : i = j
  · subst hij
    simpa [NuclearPhononRPA.comm, QuasiparticleCAR.comm] using car.comm_numberOp_a_same i
  · simpa [NuclearPhononRPA.comm, QuasiparticleCAR.comm, hij] using
      car.comm_numberOp_a_distinct_carrier i j hij

omit [Algebra ℝ A] in
private theorem comm_derivation_gen (X Y Z : A) :
    NuclearPhononRPA.comm X (Y * Z) =
      NuclearPhononRPA.comm X Y * Z + Y * NuclearPhononRPA.comm X Z := by
  dsimp [NuclearPhononRPA.comm]
  noncomm_ring

omit [Algebra ℝ A] in
private theorem comm_sum_left_gen {α : Type*} (s : Finset α) (f : α → A) (Z : A) :
    NuclearPhononRPA.comm (∑ i ∈ s, f i) Z = ∑ i ∈ s, NuclearPhononRPA.comm (f i) Z := by
  dsimp [NuclearPhononRPA.comm]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- Single-orbital number commutator with pair creation:
`[N_i, B_{jk}†] = (δ_{ij} + δ_{ik}) B_{jk}†`. -/
theorem comm_numberOp_pairCreation (car : QuasiparticleCAR ι_qp A) (i j k : ι_qp) :
    NuclearPhononRPA.comm (car.numberOp i) (car.pairCreation j k) =
      ((if i = j then (1 : ℝ) else 0) + (if i = k then 1 else 0)) • car.pairCreation j k := by
  dsimp [QuasiparticleCAR.pairCreation]
  rw [comm_derivation_gen, comm_numberOp_adag_ite, comm_numberOp_adag_ite,
    smul_mul_assoc, mul_smul_comm, add_smul]

/-- **Pair-Number `ΔN = +2` Commutator**:
`[∑ i ∈ s, N_i, B_{jk}†] = 2 • B_{jk}†` whenever `j, k ∈ s`. -/
theorem comm_totalNumberOp_pairCreation (car : QuasiparticleCAR ι_qp A) (s : Finset ι_qp)
    {j k : ι_qp} (hj : j ∈ s) (hk : k ∈ s) :
    NuclearPhononRPA.comm (totalNumberOp car s) (car.pairCreation j k) =
      (2 : ℝ) • car.pairCreation j k := by
  dsimp [totalNumberOp]
  rw [comm_sum_left_gen]
  simp_rw [comm_numberOp_pairCreation, ← Finset.sum_smul, Finset.sum_add_distrib]
  have hsj : ∑ i ∈ s, (if i = j then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · intro hnj; exact False.elim (hnj hj)
  have hsk : ∑ i ∈ s, (if i = k then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [hik]
    · intro hnk; exact False.elim (hnk hk)
  rw [hsj, hsk]
  norm_num

/-- Distinct-orbital specialization (`j ≠ k`) of the `ΔN = +2` pair-creation commutator. -/
theorem comm_totalNumberOp_pairCreation_ne (car : QuasiparticleCAR ι_qp A) (s : Finset ι_qp)
    {j k : ι_qp} (hj : j ∈ s) (hk : k ∈ s) :
    NuclearPhononRPA.comm (totalNumberOp car s) (car.pairCreation j k) =
      (2 : ℝ) • car.pairCreation j k :=
  comm_totalNumberOp_pairCreation car s hj hk

/-- Single-orbital number commutator with pair annihilation:
`[N_i, B_{jk}] = -(δ_{ij} + δ_{ik}) B_{jk}`. -/
theorem comm_numberOp_pairAnnihilation (car : QuasiparticleCAR ι_qp A) (i j k : ι_qp) :
    NuclearPhononRPA.comm (car.numberOp i) (car.pairAnnihilation j k) =
      -(((if i = j then (1 : ℝ) else 0) + (if i = k then 1 else 0)) •
        car.pairAnnihilation j k) := by
  dsimp [QuasiparticleCAR.pairAnnihilation]
  rw [comm_derivation_gen, comm_numberOp_a_ite, comm_numberOp_a_ite,
    neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, ← neg_add, ← add_smul, add_comm]

/-- **Pair-Number `ΔN = -2` Commutator**:
`[∑ i ∈ s, N_i, B_{jk}] = -(2 • B_{jk})` whenever `j, k ∈ s`. -/
theorem comm_totalNumberOp_pairAnnihilation (car : QuasiparticleCAR ι_qp A) (s : Finset ι_qp)
    {j k : ι_qp} (hj : j ∈ s) (hk : k ∈ s) :
    NuclearPhononRPA.comm (totalNumberOp car s) (car.pairAnnihilation j k) =
      -((2 : ℝ) • car.pairAnnihilation j k) := by
  dsimp [totalNumberOp]
  rw [comm_sum_left_gen]
  simp_rw [comm_numberOp_pairAnnihilation, Finset.sum_neg_distrib, ← Finset.sum_smul,
    Finset.sum_add_distrib]
  have hsj : ∑ i ∈ s, (if i = j then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [hij]
    · intro hnj; exact False.elim (hnj hj)
  have hsk : ∑ i ∈ s, (if i = k then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [hik]
    · intro hnk; exact False.elim (hnk hk)
  rw [hsj, hsk]
  norm_num

/-- Collective TDA pair creation carries exact quantum number `ΔN = +2`. -/
theorem comm_totalNumberOp_tdaPairCreation (car : QuasiparticleCAR ι_qp A) (s : Finset ι_qp)
    (pairs : Finset (ι_qp × ι_qp)) (hpairs : ∀ p ∈ pairs, p.1 ∈ s ∧ p.2 ∈ s)
    (ψ : ι_qp → ι_qp → ℝ) :
    NuclearPhononRPA.comm (totalNumberOp car s) (car.tdaPairCreation pairs ψ) =
      (2 : ℝ) • car.tdaPairCreation pairs ψ := by
  have hcomm_sum_r : ∀ (t : Finset (ι_qp × ι_qp)) (X : A) (f : ι_qp × ι_qp → A),
      NuclearPhononRPA.comm X (∑ p ∈ t, f p) = ∑ p ∈ t, NuclearPhononRPA.comm X (f p) := by
    intro t X f; dsimp [NuclearPhononRPA.comm]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hcomm_smul_r : ∀ (r : ℝ) (X Y : A),
      NuclearPhononRPA.comm X (r • Y) = r • NuclearPhononRPA.comm X Y := by
    intro r X Y; dsimp [NuclearPhononRPA.comm]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  dsimp [QuasiparticleCAR.tdaPairCreation]
  rw [hcomm_sum_r, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hcomm_smul_r, comm_totalNumberOp_pairCreation car s (hpairs p hp).1 (hpairs p hp).2,
    smul_comm]

/-- Collective TDA pair annihilation carries exact quantum number `ΔN = -2`. -/
theorem comm_totalNumberOp_tdaPairAnnihilation (car : QuasiparticleCAR ι_qp A) (s : Finset ι_qp)
    (pairs : Finset (ι_qp × ι_qp)) (hpairs : ∀ p ∈ pairs, p.1 ∈ s ∧ p.2 ∈ s)
    (ψ : ι_qp → ι_qp → ℝ) :
    NuclearPhononRPA.comm (totalNumberOp car s) (car.tdaPairAnnihilation pairs ψ) =
      -((2 : ℝ) • car.tdaPairAnnihilation pairs ψ) := by
  have hcomm_sum_r : ∀ (t : Finset (ι_qp × ι_qp)) (X : A) (f : ι_qp × ι_qp → A),
      NuclearPhononRPA.comm X (∑ p ∈ t, f p) = ∑ p ∈ t, NuclearPhononRPA.comm X (f p) := by
    intro t X f; dsimp [NuclearPhononRPA.comm]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hcomm_smul_r : ∀ (r : ℝ) (X Y : A),
      NuclearPhononRPA.comm X (r • Y) = r • NuclearPhononRPA.comm X Y := by
    intro r X Y; dsimp [NuclearPhononRPA.comm]
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
  dsimp [QuasiparticleCAR.tdaPairAnnihilation]
  rw [hcomm_sum_r, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hcomm_smul_r, comm_totalNumberOp_pairAnnihilation car s (hpairs p hp).1 (hpairs p hp).2,
    smul_neg, smul_comm]

/-- Single-orbital number commutator with neutral scattering:
`[N_i, a_p† a_q] = (δ_{ip} - δ_{iq}) a_p† a_q`. -/
theorem comm_numberOp_scatterOp (car : QuasiparticleCAR ι_qp A) (i p q : ι_qp) :
    NuclearPhononRPA.comm (car.numberOp i) (NuclearPhononRPA.scatterOp car p q) =
      ((if i = p then (1 : ℝ) else 0) - (if i = q then 1 else 0)) •
        NuclearPhononRPA.scatterOp car p q := by
  dsimp [NuclearPhononRPA.scatterOp]
  rw [comm_derivation_gen, comm_numberOp_adag_ite, comm_numberOp_a_ite,
    mul_neg, smul_mul_assoc, mul_smul_comm, ← sub_eq_add_neg, ← sub_smul]

/-- **Neutral Scattering `ΔN = 0` Separation**:
`[∑ i ∈ s, N_i, a_p† a_q] = 0` whenever `p, q ∈ s`. -/
theorem comm_totalNumberOp_scatterOp (car : QuasiparticleCAR ι_qp A) (s : Finset ι_qp)
    {p q : ι_qp} (hp : p ∈ s) (hq : q ∈ s) :
    NuclearPhononRPA.comm (totalNumberOp car s) (NuclearPhononRPA.scatterOp car p q) = 0 := by
  dsimp [totalNumberOp]
  rw [comm_sum_left_gen]
  simp_rw [comm_numberOp_scatterOp, ← Finset.sum_smul, Finset.sum_sub_distrib]
  have hsp : ∑ i ∈ s, (if i = p then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro i _ hip; simp [hip]
    · intro hnp; exact False.elim (hnp hp)
  have hsq : ∑ i ∈ s, (if i = q then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single q]
    · simp
    · intro i _ hiq; simp [hiq]
    · intro hnq; exact False.elim (hnq hq)
  rw [hsp, hsq, sub_self, zero_smul]

/-- Orbital-wise separation: `N_i` commutes with any scattering operator `a_p† a_q` on
disjoint orbitals (`i ≠ p`, `i ≠ q`) or diagonal `p = q`. -/
theorem comm_numberOp_scatterOp_disjoint (car : QuasiparticleCAR ι_qp A)
    {i p q : ι_qp} (hip : i ≠ p) (hiq : i ≠ q) :
    NuclearPhononRPA.comm (car.numberOp i) (NuclearPhononRPA.scatterOp car p q) = 0 := by
  rw [comm_numberOp_scatterOp]
  simp [hip, hiq]

theorem comm_numberOp_scatterOp_diag (car : QuasiparticleCAR ι_qp A) (i p : ι_qp) :
    NuclearPhononRPA.comm (car.numberOp i) (NuclearPhononRPA.scatterOp car p p) = 0 := by
  rw [comm_numberOp_scatterOp]
  simp

/-- Any operator `B` commuting with `car.numberOp i` (`[N_i, B] = 0`) automatically commutes
with the centered Cartan `2N_i - 1`, vacancy projector `1 - N_i`, and fermion parity `1 - 2N_i`. -/
theorem quantum_number_separation_of_numberOp_comm (car : QuasiparticleCAR ι_qp A)
    (i : ι_qp) (B : A) (hNB : NuclearPhononRPA.comm (car.numberOp i) B = 0) :
    NuclearPhononRPA.comm (car.centeredOccupationCartan i) B = 0 ∧
      NuclearPhononRPA.comm (car.vacancyProjector i) B = 0 ∧
      NuclearPhononRPA.comm (car.fermionParity i) B = 0 := by
  have hcomm : car.numberOp i * B = B * car.numberOp i := sub_eq_zero.mp hNB
  refine ⟨?_, ?_, ?_⟩ <;>
    · dsimp [NuclearPhononRPA.comm, QuasiparticleCAR.centeredOccupationCartan,
        QuasiparticleCAR.vacancyProjector, QuasiparticleCAR.fermionParity]
      noncomm_ring [hcomm]

/-- Neutral scattering `a_p† a_q` separates cleanly from `centeredOccupationCartan i`,
`vacancyProjector i`, and `fermionParity i` whenever `i ∉ {p, q}` or `p = q`. -/
theorem scatterOp_quantum_number_separation (car : QuasiparticleCAR ι_qp A)
    (i p q : ι_qp) (hsep : (i ≠ p ∧ i ≠ q) ∨ p = q) :
    NuclearPhononRPA.comm (car.numberOp i) (NuclearPhononRPA.scatterOp car p q) = 0 ∧
      NuclearPhononRPA.comm (car.centeredOccupationCartan i)
        (NuclearPhononRPA.scatterOp car p q) = 0 ∧
      NuclearPhononRPA.comm (car.vacancyProjector i)
        (NuclearPhononRPA.scatterOp car p q) = 0 ∧
      NuclearPhononRPA.comm (car.fermionParity i)
        (NuclearPhononRPA.scatterOp car p q) = 0 := by
  have hNB : NuclearPhononRPA.comm (car.numberOp i) (NuclearPhononRPA.scatterOp car p q) = 0 := by
    rcases hsep with ⟨hip, hiq⟩ | rfl
    · exact comm_numberOp_scatterOp_disjoint car hip hiq
    · exact comm_numberOp_scatterOp_diag car i p
  exact ⟨hNB, quantum_number_separation_of_numberOp_comm car i _ hNB⟩

end PairNumberAndScattering

end InfoGeometry.Physics.NuclearRPAQuantumNumberSeparation
