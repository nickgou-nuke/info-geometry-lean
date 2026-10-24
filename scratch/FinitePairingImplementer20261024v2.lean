/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ChiralCARTransport

/-! # Circular pairing implementer -- UNCOMPILED sandbox proposal

Primitive two-mode CAR only. The support is an explicit pair-occupancy
polynomial, not the ambient identity. No star assertion or new CAR carrier.
Proof scripts below require independent elaboration before promotion.
-/
namespace InfoGeometry.Sandbox.FinitePairingImplementer20261024

variable {A : Type*} [Ring A]

-- Private word reductions used to normalize the primitive CAR relations.
private theorem square_tail (x z : A) (h : x * x = 0) :
    x * (x * z) = 0 := by rw [← mul_assoc, h, zero_mul]

private theorem car_pair (x y : A) (h : x * y + y * x = 1) :
    x * y = 1 - y * x := eq_sub_of_add_eq h

private theorem car_tail (x y z : A) (h : x * y + y * x = 1) :
    x * (y * z) = z - y * (x * z) := by
  rw [← mul_assoc, car_pair x y h, sub_mul, one_mul, mul_assoc]

private theorem anti_pair (x y : A) (h : x * y + y * x = 0) :
    x * y = -(y * x) := eq_neg_of_add_eq_zero_left h

private theorem anti_tail (x y z : A) (h : x * y + y * x = 0) :
    x * (y * z) = -(y * (x * z)) := by
  rw [← mul_assoc, anti_pair x y h, neg_mul, mul_assoc]

/-- Pair annihilation minus pair creation, with native current conventions. -/
def current (p P q Q : A) : A := q * p - P * Q

/-- Support of the empty/doubly occupied pair sectors. -/
def pairSupport (p P q Q : A) : A :=
  (q * p) * (P * Q) + (P * Q) * (q * p)

variable (p P q Q : A)
variable (hp : p * p = 0) (hP : P * P = 0)
variable (hq : q * q = 0) (hQ : Q * Q = 0)
variable (hpP : p * P + P * p = 1) (hqQ : q * Q + Q * q = 1)
variable (hpq : p * q + q * p = 0) (hPQ : P * Q + Q * P = 0)
variable (hpQ : p * Q + Q * p = 0) (hqP : q * P + P * q = 0)
include hp hP hq hQ hpP hqQ hpq hPQ hpQ hqP

/-- Readback as the sum of empty and double-occupancy supports. -/
theorem pairSupport_eq_occupancy :
    pairSupport p P q Q = (p * P) * (q * Q) + (P * p) * (Q * q) := by
  simp (disch := assumption) only [pairSupport, mul_add, add_mul,
    mul_sub, sub_mul, neg_mul, mul_neg, mul_assoc, square_tail,
    car_tail, anti_tail, car_pair, anti_pair, hp, hP, hq, hQ,
    mul_zero, zero_mul, one_mul, mul_one, neg_neg, sub_zero, zero_sub,
    add_zero, zero_add]
  noncomm_ring

theorem current_sq :
    current p P q Q * current p P q Q = -pairSupport p P q Q := by
  simp (disch := assumption) only [current, pairSupport, mul_add, add_mul,
    mul_sub, sub_mul, neg_mul, mul_neg, mul_assoc, square_tail,
    car_tail, anti_tail, car_pair, anti_pair, hp, hP, hq, hQ,
    mul_zero, zero_mul, one_mul, mul_one, neg_neg, sub_zero, zero_sub,
    add_zero, zero_add]
  noncomm_ring

theorem pairSupport_sq :
    pairSupport p P q Q * pairSupport p P q Q = pairSupport p P q Q := by
  simp (disch := assumption) only [current, pairSupport, mul_add, add_mul,
    mul_sub, sub_mul, neg_mul, mul_neg, mul_assoc, square_tail,
    car_tail, anti_tail, car_pair, anti_pair, hp, hP, hq, hQ,
    mul_zero, zero_mul, one_mul, mul_one, neg_neg, sub_zero, zero_sub,
    add_zero, zero_add]
  noncomm_ring

theorem pairSupport_mul_current :
    pairSupport p P q Q * current p P q Q = current p P q Q := by
  simp (disch := assumption) only [current, pairSupport, mul_add, add_mul,
    mul_sub, sub_mul, neg_mul, mul_neg, mul_assoc, square_tail,
    car_tail, anti_tail, car_pair, anti_pair, hp, hP, hq, hQ,
    mul_zero, zero_mul, one_mul, mul_one, neg_neg, sub_zero, zero_sub,
    add_zero, zero_add]
  noncomm_ring

theorem current_mul_pairSupport :
    current p P q Q * pairSupport p P q Q = current p P q Q := by
  simp (disch := assumption) only [current, pairSupport, mul_add, add_mul,
    mul_sub, sub_mul, neg_mul, mul_neg, mul_assoc, square_tail,
    car_tail, anti_tail, car_pair, anti_pair, hp, hP, hq, hQ,
    mul_zero, zero_mul, one_mul, mul_one, neg_neg, sub_zero, zero_sub,
    add_zero, zero_add]
  noncomm_ring

section Scalars
variable {R : Type*} [CommRing R] [Algebra R A]

/-- The identity on the complementary sector plus a circular pair-sector rotor. -/
def rotor (p P q Q : A) (c s : R) : A :=
  1 + (c - 1) • pairSupport p P q Q + s • current p P q Q

/-- Polynomial inverse defect; normalization is needed only to make this one. -/
theorem rotor_mul_reverse (c s : R) :
    rotor p P q Q c s * rotor p P q Q c (-s) =
      1 + (c * c + s * s - 1) • pairSupport p P q Q := by
  have hTT := current_sq p P q Q hp hP hq hQ hpP hqQ hpq hPQ hpQ hqP
  have hEE := pairSupport_sq p P q Q hp hP hq hQ hpP hqQ hpq hPQ hpQ hqP
  have hET := pairSupport_mul_current p P q Q hp hP hq hQ hpP hqQ hpq hPQ hpQ hqP
  have hTE := current_mul_pairSupport p P q Q hp hP hq hQ hpP hqQ hpq hPQ hpQ hqP
  simp only [rotor, add_mul, mul_add, smul_mul_smul, one_mul, mul_one,
    hTT, hEE, hET, hTE, smul_neg]
  module

/-- Both inverse orders are consequences of CAR and scalar normalization. -/
def rotorUnit (c s : R) (hcs : c * c + s * s = 1) : Aˣ where
  val := rotor p P q Q c s
  inv := rotor p P q Q c (-s)
  val_inv := by
    rw [rotor_mul_reverse p P q Q hp hP hq hQ hpP hqQ hpq hPQ hpQ hqP, hcs]
    simp
  inv_val := by
    have h := rotor_mul_reverse p P q Q hp hP hq hQ hpP hqQ hpq hPQ hpQ hqP c (-s)
    simpa [hcs] using h

/-- Exact finite action; the polynomial identity needs no normalization. -/
theorem rotor_annihilator_one (c s : R) :
    rotor p P q Q c s * p * rotor p P q Q c (-s) = c • p + s • Q := by
  simp (disch := assumption) only [rotor, current, pairSupport,
    mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, smul_sub,
    smul_neg, mul_assoc, square_tail, car_tail, anti_tail, car_pair, anti_pair,
    hp, hP, hq, hQ, mul_zero, zero_mul, one_mul, mul_one,
    neg_neg, sub_zero, zero_sub, add_zero, zero_add, smul_zero]
  module

/-- Exact finite action; the polynomial identity needs no normalization. -/
theorem rotor_creator_two (c s : R) :
    rotor p P q Q c s * Q * rotor p P q Q c (-s) = c • Q - s • p := by
  simp (disch := assumption) only [rotor, current, pairSupport,
    mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, smul_sub,
    smul_neg, mul_assoc, square_tail, car_tail, anti_tail, car_pair, anti_pair,
    hp, hP, hq, hQ, mul_zero, zero_mul, one_mul, mul_one,
    neg_neg, sub_zero, zero_sub, add_zero, zero_add, smul_zero]
  module

/-- Exact finite action; the polynomial identity needs no normalization. -/
theorem rotor_annihilator_two (c s : R) :
    rotor p P q Q c s * q * rotor p P q Q c (-s) = c • q - s • P := by
  simp (disch := assumption) only [rotor, current, pairSupport,
    mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, smul_sub,
    smul_neg, mul_assoc, square_tail, car_tail, anti_tail, car_pair, anti_pair,
    hp, hP, hq, hQ, mul_zero, zero_mul, one_mul, mul_one,
    neg_neg, sub_zero, zero_sub, add_zero, zero_add, smul_zero]
  module

/-- Exact finite action; the polynomial identity needs no normalization. -/
theorem rotor_creator_one (c s : R) :
    rotor p P q Q c s * P * rotor p P q Q c (-s) = c • P + s • q := by
  simp (disch := assumption) only [rotor, current, pairSupport,
    mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg,
    smul_mul_assoc, mul_smul_comm, smul_smul, smul_add, smul_sub,
    smul_neg, mul_assoc, square_tail, car_tail, anti_tail, car_pair, anti_pair,
    hp, hP, hq, hQ, mul_zero, zero_mul, one_mul, mul_one,
    neg_neg, sub_zero, zero_sub, add_zero, zero_add, smul_zero]
  module

end Scalars
end InfoGeometry.Sandbox.FinitePairingImplementer20261024
