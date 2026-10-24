/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge
import InfoGeometry.Physics.NuclearWignerSupermultipletSymmetry
import InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
import InfoGeometry.Canonical.SL2SpinorLadder

/-!
# Nuclear Cartan, projector, parity, and quantum-number bridge

This file closes a finite algebraic interface already implicit in the nuclear
owners.  It does not identify the nuclear quasiparticle algebra with the full
five-graded exceptional corridor.  Instead it proves that each CAR mode carries
an exact `sl₂`-shaped Cartan/raising/lowering packet and records the matching
relation shape already present in `SL2SpinorLadder`.

It also packages the occupation idempotents as complementary projectors, the
corresponding fermion-parity involution, a two-valued occupation quantum-number
readout, and the existing spin/isospin chirality involutions.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearCartanProjectorParityBridge

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
open InfoGeometry.Canonical.SL2SpinorLadder

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
open InfoGeometry.Canonical.SL2SpinorLadder

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

end InfoGeometry.Physics.NuclearCartanProjectorParityBridge

namespace InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

variable (car : QuasiparticleCAR ι A)

/-- Centered occupation Cartan element `Hᵢ = 2Nᵢ - 1`. -/
def centeredOccupationCartan (i : ι) : A :=
  car.numberOp i + car.numberOp i - 1

/-- Complementary vacancy projector `1 - Nᵢ`. -/
def vacancyProjector (i : ι) : A :=
  1 - car.numberOp i

/-- Fermion parity of one quasiparticle mode: `(-1)^N = 1 - 2N`. -/
def fermionParity (i : ι) : A :=
  1 - car.numberOp i - car.numberOp i

/-- The number operator annihilates an annihilation operator on its right. -/
theorem numberOp_mul_a_same (i : ι) :
    car.numberOp i * car.a i = 0 := by
  unfold numberOp
  calc
    (car.adag i * car.a i) * car.a i =
        car.adag i * (car.a i * car.a i) := by simp [mul_assoc]
    _ = 0 := by rw [car.a_sq i]; simp

/-- The annihilation operator followed by the number operator returns the annihilation operator. -/
theorem a_mul_numberOp_same (i : ι) :
    car.a i * car.numberOp i = car.a i := by
  unfold numberOp
  calc
    car.a i * (car.adag i * car.a i) =
        (car.a i * car.adag i) * car.a i := by simp [mul_assoc]
    _ = (1 - car.adag i * car.a i) * car.a i := by
      rw [car.a_mul_adag_same i]
    _ = car.a i - (car.adag i * car.a i) * car.a i := by
      rw [sub_mul, one_mul]
    _ = car.a i := by
      change car.a i - car.numberOp i * car.a i = car.a i
      rw [numberOp_mul_a_same]
      simp

/-- The number operator followed by creation returns the creation operator. -/
theorem numberOp_mul_adag_same (i : ι) :
    car.numberOp i * car.adag i = car.adag i := by
  unfold numberOp
  calc
    (car.adag i * car.a i) * car.adag i =
        car.adag i * (car.a i * car.adag i) := by simp [mul_assoc]
    _ = car.adag i * (1 - car.adag i * car.a i) := by
      rw [car.a_mul_adag_same i]
    _ = car.adag i - car.adag i * (car.adag i * car.a i) := by
      rw [mul_sub, mul_one]
    _ = car.adag i - (car.adag i * car.adag i) * car.a i := by
      simp [mul_assoc]
    _ = car.adag i := by rw [car.adag_sq i]; simp

/-- Creation followed by the number operator vanishes. -/
theorem adag_mul_numberOp_same (i : ι) :
    car.adag i * car.numberOp i = 0 := by
  unfold numberOp
  calc
    car.adag i * (car.adag i * car.a i) =
        (car.adag i * car.adag i) * car.a i := by simp [mul_assoc]
    _ = 0 := by rw [car.adag_sq i]; simp

/-- Number-annihilation commutator: `[Nᵢ,aᵢ] = -aᵢ`. -/
theorem comm_numberOp_a_same (i : ι) :
    comm (car.numberOp i) (car.a i) = -car.a i := by
  unfold comm
  rw [numberOp_mul_a_same, a_mul_numberOp_same]
  simp

/-- Cartan/creation relation: `[Hᵢ,aᵢ†] = 2aᵢ†`. -/
theorem comm_centeredOccupationCartan_adag (i : ι) :
    comm (car.centeredOccupationCartan i) (car.adag i) =
      car.adag i + car.adag i := by
  unfold centeredOccupationCartan comm
  calc
    (car.numberOp i + car.numberOp i - 1) * car.adag i -
        car.adag i * (car.numberOp i + car.numberOp i - 1) =
      comm (car.numberOp i) (car.adag i) +
        comm (car.numberOp i) (car.adag i) := by
      simp only [comm]
      noncomm_ring
    _ = car.adag i + car.adag i := by
      rw [car.comm_numberOp_adag_same i]

/-- Cartan/annihilation relation: `[Hᵢ,aᵢ] = -2aᵢ`. -/
theorem comm_centeredOccupationCartan_a (i : ι) :
    comm (car.centeredOccupationCartan i) (car.a i) =
      -(car.a i + car.a i) := by
  unfold centeredOccupationCartan comm
  calc
    (car.numberOp i + car.numberOp i - 1) * car.a i -
        car.a i * (car.numberOp i + car.numberOp i - 1) =
      comm (car.numberOp i) (car.a i) +
        comm (car.numberOp i) (car.a i) := by
      simp only [comm]
      noncomm_ring
    _ = -(car.a i + car.a i) := by
      rw [comm_numberOp_a_same]
      abel

omit [Algebra ℝ A] in
/-- Creation/annihilation commutator closes on the centered occupation Cartan element. -/
theorem comm_adag_a_eq_centeredOccupationCartan (i : ι) :
    comm (car.adag i) (car.a i) = car.centeredOccupationCartan i := by
  unfold comm centeredOccupationCartan numberOp
  rw [car.a_mul_adag_same i]
  noncomm_ring

/-- The vacancy operator is an idempotent projector. -/
theorem vacancyProjector_idempotent (i : ι) :
    car.vacancyProjector i * car.vacancyProjector i =
      car.vacancyProjector i := by
  unfold vacancyProjector
  have hN := car.numberOp_idempotent i
  calc
    (1 - car.numberOp i) * (1 - car.numberOp i) =
        1 - car.numberOp i - car.numberOp i +
          car.numberOp i * car.numberOp i := by noncomm_ring
    _ = 1 - car.numberOp i := by rw [hN]; noncomm_ring

omit [Algebra ℝ A] in
/-- Occupied and vacant projectors resolve the identity. -/
theorem occupation_vacancy_sum (i : ι) :
    car.numberOp i + car.vacancyProjector i = 1 := by
  unfold vacancyProjector
  noncomm_ring

/-- Occupied then vacant projection vanishes. -/
theorem occupation_mul_vacancy (i : ι) :
    car.numberOp i * car.vacancyProjector i = 0 := by
  unfold vacancyProjector
  rw [mul_sub, mul_one, car.numberOp_idempotent i]
  exact sub_self _

/-- Vacant then occupied projection vanishes. -/
theorem vacancy_mul_occupation (i : ι) :
    car.vacancyProjector i * car.numberOp i = 0 := by
  unfold vacancyProjector
  rw [sub_mul, one_mul, car.numberOp_idempotent i]
  exact sub_self _

/-- The one-mode fermion parity is an involution. -/
theorem fermionParity_sq (i : ι) :
    car.fermionParity i * car.fermionParity i = 1 := by
  unfold fermionParity
  have hN := car.numberOp_idempotent i
  calc
    (1 - car.numberOp i - car.numberOp i) *
        (1 - car.numberOp i - car.numberOp i) =
      1 - car.numberOp i - car.numberOp i - car.numberOp i - car.numberOp i +
        car.numberOp i * car.numberOp i +
        car.numberOp i * car.numberOp i +
        car.numberOp i * car.numberOp i +
        car.numberOp i * car.numberOp i := by noncomm_ring
    _ = 1 := by rw [hN]; noncomm_ring

/-- Fermion parity anticommutes with creation. -/
theorem fermionParity_anticomm_adag (i : ι) :
    car.fermionParity i * car.adag i +
      car.adag i * car.fermionParity i = 0 := by
  have h₁ := car.numberOp_mul_adag_same i
  have h₂ := car.adag_mul_numberOp_same i
  unfold fermionParity
  calc
    (1 - car.numberOp i - car.numberOp i) * car.adag i +
        car.adag i * (1 - car.numberOp i - car.numberOp i) =
      car.adag i + car.adag i - car.numberOp i * car.adag i -
        car.numberOp i * car.adag i - car.adag i * car.numberOp i -
        car.adag i * car.numberOp i := by noncomm_ring
    _ = 0 := by rw [h₁, h₂]; module

/-- Fermion parity anticommutes with annihilation. -/
theorem fermionParity_anticomm_a (i : ι) :
    car.fermionParity i * car.a i +
      car.a i * car.fermionParity i = 0 := by
  have h₁ := car.numberOp_mul_a_same i
  have h₂ := car.a_mul_numberOp_same i
  unfold fermionParity
  calc
    (1 - car.numberOp i - car.numberOp i) * car.a i +
        car.a i * (1 - car.numberOp i - car.numberOp i) =
      car.a i + car.a i - car.numberOp i * car.a i -
        car.numberOp i * car.a i - car.a i * car.numberOp i -
        car.a i * car.numberOp i := by noncomm_ring
    _ = 0 := by rw [h₁, h₂]; module

/-- Conjugation by fermion parity reverses the creation operator. -/
theorem fermionParity_conj_adag (i : ι) :
    car.fermionParity i * car.adag i * car.fermionParity i = -car.adag i := by
  have hanti := car.fermionParity_anticomm_adag i
  have hsq := car.fermionParity_sq i
  calc
    car.fermionParity i * car.adag i * car.fermionParity i =
        -(car.adag i * car.fermionParity i) * car.fermionParity i := by
      have h : car.fermionParity i * car.adag i =
          -(car.adag i * car.fermionParity i) := by
        exact (add_eq_zero_iff_eq_neg).mp hanti
      rw [h]
    _ = -car.adag i *
        (car.fermionParity i * car.fermionParity i) := by
      simp [mul_assoc]
    _ = -car.adag i := by rw [hsq]; simp

/-- Conjugation by fermion parity reverses the annihilation operator. -/
theorem fermionParity_conj_a (i : ι) :
    car.fermionParity i * car.a i * car.fermionParity i = -car.a i := by
  have hanti := car.fermionParity_anticomm_a i
  have hsq := car.fermionParity_sq i
  calc
    car.fermionParity i * car.a i * car.fermionParity i =
        -(car.a i * car.fermionParity i) * car.fermionParity i := by
      have h : car.fermionParity i * car.a i =
          -(car.a i * car.fermionParity i) := by
        exact (add_eq_zero_iff_eq_neg).mp hanti
      rw [h]
    _ = -car.a i *
        (car.fermionParity i * car.fermionParity i) := by
      simp [mul_assoc]
    _ = -car.a i := by rw [hsq]; simp

/-- One-mode nuclear `sl₂` relation packet derived only from CAR. -/
theorem nuclear_sl2_packet (i : ι) :
    comm (car.centeredOccupationCartan i) (car.adag i) =
        car.adag i + car.adag i ∧
      comm (car.centeredOccupationCartan i) (car.a i) =
        -(car.a i + car.a i) ∧
      comm (car.adag i) (car.a i) = car.centeredOccupationCartan i :=
  ⟨car.comm_centeredOccupationCartan_adag i,
    car.comm_centeredOccupationCartan_a i,
    car.comm_adag_a_eq_centeredOccupationCartan i⟩

end InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR

namespace InfoGeometry.Physics.NuclearCartanProjectorParityBridge

variable {ι : Type*} [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation
open InfoGeometry.Canonical.SL2SpinorLadder

/-! ## Finite occupation quantum-number readout -/

/-- The two exact one-mode occupation labels. -/
inductive OccupationQuantumNumber where
  | vacant
  | occupied
  deriving DecidableEq, Repr

namespace OccupationQuantumNumber

/-- Integer occupation readout. -/
def value : OccupationQuantumNumber → ℤ
  | vacant => 0
  | occupied => 1

/-- Centered Cartan weight `2n-1`. -/
def cartanWeight : OccupationQuantumNumber → ℤ
  | vacant => -1
  | occupied => 1

/-- Fermion-parity weight `(-1)^n`. -/
def parityWeight : OccupationQuantumNumber → ℤ
  | vacant => 1
  | occupied => -1

@[simp] theorem cartanWeight_eq_two_value_sub_one (q : OccupationQuantumNumber) :
    q.cartanWeight = 2 * q.value - 1 := by
  cases q <;> rfl

@[simp] theorem parityWeight_eq_one_sub_two_value (q : OccupationQuantumNumber) :
    q.parityWeight = 1 - 2 * q.value := by
  cases q <;> rfl

@[simp] theorem parityWeight_sq (q : OccupationQuantumNumber) :
    q.parityWeight ^ 2 = 1 := by
  cases q <;> norm_num [parityWeight]

end OccupationQuantumNumber

/-- Projector selected by a one-mode occupation quantum number. -/
def occupationProjector
    {ι : Type*} [DecidableEq ι] {A : Type*} [Ring A] [Algebra ℝ A]
    (car : QuasiparticleCAR ι A) (i : ι) : OccupationQuantumNumber → A
  | .vacant => car.vacancyProjector i
  | .occupied => car.numberOp i

/-- Every occupation quantum-number sector is represented by an idempotent. -/
theorem occupationProjector_idempotent
    {ι : Type*} [DecidableEq ι] {A : Type*} [Ring A] [Algebra ℝ A]
    (car : QuasiparticleCAR ι A) (i : ι) (q : OccupationQuantumNumber) :
    occupationProjector car i q * occupationProjector car i q =
      occupationProjector car i q := by
  cases q
  · exact car.vacancyProjector_idempotent i
  · exact car.numberOp_idempotent i

/-! ## Wigner isospin Cartan and projectors -/

/-- The normalized Wigner-isospin Cartan involution `2T₃ = σ₃`. -/
def isospinCartan : Matrix (Fin 2) (Fin 2) ℂ :=
  (2 : ℂ) • isospin3

/-- `2T₃` is exactly the third Pauli matrix. -/
theorem isospinCartan_eq_pauli3 : isospinCartan = pauli3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [isospinCartan,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.isospin3,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli3]

/-- The Wigner-isospin Cartan readout is an involution. -/
theorem isospinCartan_sq : isospinCartan * isospinCartan = 1 := by
  rw [isospinCartan_eq_pauli3, pauli3_sq]

/-- Positive `T₃` spectral projector. -/
def isospinPositiveProjector : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 0]

/-- Negative `T₃` spectral projector. -/
def isospinNegativeProjector : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; 0, 1]

/-- Positive isospin projector is idempotent. -/
theorem isospinPositiveProjector_idempotent :
    isospinPositiveProjector * isospinPositiveProjector =
      isospinPositiveProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [isospinPositiveProjector]

/-- Negative isospin projector is idempotent. -/
theorem isospinNegativeProjector_idempotent :
    isospinNegativeProjector * isospinNegativeProjector =
      isospinNegativeProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [isospinNegativeProjector]

/-- The two `T₃` projectors resolve the identity. -/
theorem isospinProjector_sum :
    isospinPositiveProjector + isospinNegativeProjector = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [isospinPositiveProjector, isospinNegativeProjector]

/-- The two `T₃` projectors are orthogonal. -/
theorem isospinProjector_orthogonal :
    isospinPositiveProjector * isospinNegativeProjector = 0 ∧
      isospinNegativeProjector * isospinPositiveProjector = 0 := by
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [isospinPositiveProjector, isospinNegativeProjector]

@[simp] theorem star_isospinPositiveProjector :
    star isospinPositiveProjector = isospinPositiveProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [isospinPositiveProjector]

@[simp] theorem star_isospinNegativeProjector :
    star isospinNegativeProjector = isospinNegativeProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [isospinNegativeProjector]

/-- Mixed-isospin operator state `E_{00} + E_{01}` in `Matrix (Fin 2) (Fin 2) ℂ`. -/
def isospinMixedState : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 1; 0, 0]

/-- Mixed-isospin state does not commute with the positive isospin projector. -/
theorem isospinMixedState_mul_positiveProjector_noncomm :
    isospinMixedState * isospinPositiveProjector ≠
      isospinPositiveProjector * isospinMixedState := by
  intro h_eq
  have h01 := congr_fun (congr_fun h_eq 0) 1
  norm_num [isospinMixedState, isospinPositiveProjector, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Left spin action commutes with right Peirce isospin projection by matrix associativity. -/
theorem left_spin_right_isospin_comm (S χ : Matrix (Fin 2) (Fin 2) ℂ) :
    (S * χ) * isospinPositiveProjector = S * (χ * isospinPositiveProjector) ∧
      (S * χ) * isospinNegativeProjector = S * (χ * isospinNegativeProjector) :=
  ⟨mul_assoc S χ isospinPositiveProjector, mul_assoc S χ isospinNegativeProjector⟩

/-- Cross-isospin Gram bilinear localizes to the off-diagonal Peirce corner. -/
theorem mixed_isospin_gram_corner (χ : Matrix (Fin 2) (Fin 2) ℂ) :
    star (χ * isospinPositiveProjector) * (χ * isospinNegativeProjector) =
      isospinPositiveProjector * (star χ * χ) * isospinNegativeProjector := by
  rw [star_mul, star_isospinPositiveProjector]
  simp only [mul_assoc]

/-- Cross-isospin Gram bilinear has identically vanishing trace. -/
theorem trace_mixed_isospin_gram_zero (χ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (star (χ * isospinPositiveProjector) * (χ * isospinNegativeProjector)) = 0 := by
  rw [mixed_isospin_gram_corner,
      Matrix.trace_mul_comm (isospinPositiveProjector * (star χ * χ)) isospinNegativeProjector,
      ← mul_assoc, isospinProjector_orthogonal.2, zero_mul, Matrix.trace_zero]

/-- Diagonal Peirce projection of the Gram operator decomposes into positive and negative isospin densities. -/
theorem diagonal_isospin_gram_decomposition (χ : Matrix (Fin 2) (Fin 2) ℂ) :
    isospinPositiveProjector * (star χ * χ) * isospinPositiveProjector +
      isospinNegativeProjector * (star χ * χ) * isospinNegativeProjector =
      star (χ * isospinPositiveProjector) * (χ * isospinPositiveProjector) +
      star (χ * isospinNegativeProjector) * (χ * isospinNegativeProjector) := by
  rw [star_mul, star_mul, star_isospinPositiveProjector, star_isospinNegativeProjector]
  simp only [mul_assoc]

theorem trace_isospinPositiveProjector_sandwich (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (isospinPositiveProjector * X * isospinPositiveProjector) =
      Matrix.trace (isospinPositiveProjector * X) := by
  rw [Matrix.trace_mul_comm (isospinPositiveProjector * X) isospinPositiveProjector,
      ← mul_assoc, isospinPositiveProjector_idempotent]

theorem trace_isospinNegativeProjector_sandwich (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (isospinNegativeProjector * X * isospinNegativeProjector) =
      Matrix.trace (isospinNegativeProjector * X) := by
  rw [Matrix.trace_mul_comm (isospinNegativeProjector * X) isospinNegativeProjector,
      ← mul_assoc, isospinNegativeProjector_idempotent]

/-- Trace of the full Gram operator equals the sum of the positive and negative isospin traces. -/
theorem trace_isospin_gram_decomposition (χ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (star χ * χ) =
      Matrix.trace (star (χ * isospinPositiveProjector) * (χ * isospinPositiveProjector)) +
      Matrix.trace (star (χ * isospinNegativeProjector) * (χ * isospinNegativeProjector)) := by
  rw [← Matrix.trace_add, ← diagonal_isospin_gram_decomposition, Matrix.trace_add,
      trace_isospinPositiveProjector_sandwich, trace_isospinNegativeProjector_sandwich,
      ← Matrix.trace_add, ← add_mul, isospinProjector_sum, one_mul]

/-- The Cartan involution is the difference of the two isospin projectors. -/
theorem isospinCartan_projector_difference :
    isospinCartan = isospinPositiveProjector - isospinNegativeProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [isospinCartan,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.isospin3,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli3,
      isospinPositiveProjector, isospinNegativeProjector]

/-- Wigner `T₊` has Cartan weight `+2` for the normalized Cartan `2T₃`. -/
theorem isospinCartan_comm_plus :
    isospinCartan * isospinPlus - isospinPlus * isospinCartan =
      (2 : ℂ) • isospinPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [isospinCartan,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.isospin3,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.isospinPlus,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli1,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli2,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli3]

/-- Wigner `T₋` has Cartan weight `-2` for the normalized Cartan `2T₃`. -/
theorem isospinCartan_comm_minus :
    isospinCartan * isospinMinus - isospinMinus * isospinCartan =
      (-2 : ℂ) • isospinMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [isospinCartan,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.isospin3,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.isospinMinus,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli1,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli2,
      InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli3]

/-- The Wigner raising/lowering commutator closes on the normalized Cartan. -/
theorem isospin_plus_minus_comm_eq_cartan :
    isospinPlus * isospinMinus - isospinMinus * isospinPlus =
      isospinCartan := by
  rw [isospin_comm_plus_minus, isospinCartan]

/-- Raising and lowering Wigner isospin operators do not commute. -/
theorem isospin_plus_minus_noncomm :
    isospinPlus * isospinMinus ≠ isospinMinus * isospinPlus := by
  intro h_eq
  have h_sub : isospinPlus * isospinMinus - isospinMinus * isospinPlus = 0 :=
    sub_eq_zero.mpr h_eq
  rw [isospin_plus_minus_comm_eq_cartan, isospinCartan_eq_pauli3] at h_sub
  have h00 := congr_fun (congr_fun h_sub 0) 0
  norm_num [InfoGeometry.Physics.NuclearWignerSupermultiplet.pauli3] at h00

/-- Wigner-isospin `sl₂` packet in the same normalization as the CAR Cartan packet. -/
theorem wigner_isospin_sl2_packet :
    isospinCartan * isospinPlus - isospinPlus * isospinCartan =
        (2 : ℂ) • isospinPlus ∧
      isospinCartan * isospinMinus - isospinMinus * isospinCartan =
        (-2 : ℂ) • isospinMinus ∧
      isospinPlus * isospinMinus - isospinMinus * isospinPlus =
        isospinCartan :=
  ⟨isospinCartan_comm_plus,
    isospinCartan_comm_minus,
    isospin_plus_minus_comm_eq_cartan⟩

/-! The native Wigner packet above is intentionally kept independent from the
tensor-product carrier; no global unit instance is required here. -/

theorem canonical_sl2_cartan_packet :
    Alg.br Alg.basisH Alg.basisE = (2 : ℝ) • Alg.basisE ∧
      Alg.br Alg.basisH Alg.basisF = (-2 : ℝ) • Alg.basisF ∧
      Alg.br Alg.basisE Alg.basisF = Alg.basisH := by
  constructor
  · norm_num [Alg.br, Alg.basisH, Alg.basisE]
  constructor
  · norm_num [Alg.br, Alg.basisH, Alg.basisF]
  · norm_num [Alg.br, Alg.basisE, Alg.basisF, Alg.basisH]

/-- Closed structural dictionary: nuclear quasiparticle Cartan, Wigner isospin
Cartan, and the canonical five-graded `sl₂` owner all realize the same three
normalized bracket equations in their native carriers. -/
theorem nuclear_cartan_relation_shape_packet
    {ι : Type*} [DecidableEq ι] {A : Type*} [Ring A] [Algebra ℝ A]
    (car : QuasiparticleCAR ι A) (i : ι) :
    (comm (car.centeredOccupationCartan i) (car.adag i) =
        car.adag i + car.adag i ∧
      comm (car.centeredOccupationCartan i) (car.a i) =
        -(car.a i + car.a i) ∧
      comm (car.adag i) (car.a i) = car.centeredOccupationCartan i) ∧
    (isospinCartan * isospinPlus - isospinPlus * isospinCartan =
        (2 : ℂ) • isospinPlus ∧
      isospinCartan * isospinMinus - isospinMinus * isospinCartan =
        (-2 : ℂ) • isospinMinus ∧
      isospinPlus * isospinMinus - isospinMinus * isospinPlus =
        isospinCartan) ∧
    (Alg.br Alg.basisH Alg.basisE = (2 : ℝ) • Alg.basisE ∧
      Alg.br Alg.basisH Alg.basisF = (-2 : ℝ) • Alg.basisF ∧
      Alg.br Alg.basisE Alg.basisF = Alg.basisH) :=
  ⟨car.nuclear_sl2_packet i,
    wigner_isospin_sl2_packet,
    canonical_sl2_cartan_packet⟩

end InfoGeometry.Physics.NuclearCartanProjectorParityBridge
