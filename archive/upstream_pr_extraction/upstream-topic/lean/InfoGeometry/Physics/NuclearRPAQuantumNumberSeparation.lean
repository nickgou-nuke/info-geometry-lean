import Mathlib.Tactic
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

end InfoGeometry.Physics.NuclearRPAQuantumNumberSeparation
