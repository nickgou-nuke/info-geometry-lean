/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Quadratic commutator expansion in a noncommutative ring

This file records the operator identity used when quadratic generators are
written as products of two noncommuting factors.  No commutativity assumption
is made on the coefficient ring.
-/

namespace InfoGeometry.OperatorAlgebra

section

variable {A : Type*} [Ring A]

def quadraticCommutator (x y : A) : A := x * y - y * x

def quadraticAnticommutator (x y : A) : A := x * y + y * x

def grandCanonicalOperator
    (β H μ N μχ Q : A) : A :=
  β * (H - μ * N - μχ * Q)

theorem RingHom.map_grandCanonicalOperator
    {B : Type*} [Ring B] (φ : A →+* B)
    (β H μ N μχ Q : A) :
    φ (grandCanonicalOperator β H μ N μχ Q) =
      grandCanonicalOperator (φ β) (φ H) (φ μ) (φ N) (φ μχ) (φ Q) := by
  simp [grandCanonicalOperator]

theorem quadraticCommutator_add (x y z : A) :
    quadraticCommutator (x + y) z =
      quadraticCommutator x z + quadraticCommutator y z := by
  dsimp [quadraticCommutator]
  noncomm_ring

theorem quadraticCommutator_sub (x y z : A) :
    quadraticCommutator (x - y) z =
      quadraticCommutator x z - quadraticCommutator y z := by
  dsimp [quadraticCommutator]
  noncomm_ring

theorem quadraticCommutator_mul_left_of_commutes
    (c x y : A) (hcy : c * y = y * c) :
    quadraticCommutator (c * x) y =
      c * quadraticCommutator x y := by
  dsimp [quadraticCommutator]
  calc
    c * x * y - y * (c * x) = c * x * y - c * y * x := by
      rw [← mul_assoc, hcy, mul_assoc]
    _ = c * (x * y - y * x) := by
      rw [mul_sub]
      simp only [mul_assoc]

theorem grandCanonicalOperator_commutator
    (β H μ N μχ Q : A)
    (hβQ : β * Q = Q * β)
    (hμQ : μ * Q = Q * μ)
    (hμχQ : μχ * Q = Q * μχ) :
    quadraticCommutator (grandCanonicalOperator β H μ N μχ Q) Q =
      β * (quadraticCommutator H Q -
        μ * quadraticCommutator N Q -
        μχ * quadraticCommutator Q Q) := by
  dsimp [grandCanonicalOperator]
  rw [quadraticCommutator_mul_left_of_commutes β
    (H - μ * N - μχ * Q) Q hβQ]
  rw [quadraticCommutator_sub, quadraticCommutator_sub]
  rw [quadraticCommutator_mul_left_of_commutes μ N Q hμQ]
  rw [quadraticCommutator_mul_left_of_commutes μχ Q Q hμχQ]

theorem grandCanonicalOperator_commutes_of_conserved
    (β H μ N μχ Q : A)
    (hβQ : β * Q = Q * β)
    (hμQ : μ * Q = Q * μ)
    (hμχQ : μχ * Q = Q * μχ)
    (hHQ : quadraticCommutator H Q = 0)
    (hNQ : quadraticCommutator N Q = 0) :
    quadraticCommutator (grandCanonicalOperator β H μ N μχ Q) Q = 0 := by
  have hQQ : quadraticCommutator Q Q = 0 := by
    dsimp [quadraticCommutator]
    exact sub_self _
  rw [grandCanonicalOperator_commutator β H μ N μχ Q hβQ hμQ hμχQ]
  simp [hHQ, hNQ, hQQ]

theorem commutator_mul_derivation (a x y : A) :
    quadraticCommutator a (x * y) =
      quadraticCommutator a x * y + x * quadraticCommutator a y := by
  dsimp [quadraticCommutator]
  noncomm_ring

theorem mul_commutator_derivation (a x y : A) :
    quadraticCommutator (x * y) a =
      x * quadraticCommutator y a + quadraticCommutator x a * y := by
  dsimp [quadraticCommutator]
  noncomm_ring

theorem RingHom.map_quadraticCommutator
    {B : Type*} [Ring B] (f : A →+* B) (x y : A) :
    f (quadraticCommutator x y) =
      quadraticCommutator (f x) (f y) := by
  simp [quadraticCommutator, map_sub, map_mul]

theorem quadratic_commutator_expansion (a b c d : A) :
    quadraticCommutator (a * b) (c * d) =
      a * quadraticAnticommutator b c * d
        - a * c * quadraticAnticommutator b d
        + quadraticAnticommutator a c * d * b
        - c * quadraticAnticommutator a d * b := by
  dsimp [quadraticCommutator, quadraticAnticommutator]
  noncomm_ring

/-- Negative CAR contractions give the matrix Lie bracket for the signed
bilinears. This is a Lie bracket identity, not a matrix-unit product law or
an identification with a general linear Lie superalgebra. -/
theorem negative_car_bilinear_commutator {ι : Type*} [DecidableEq ι]
    (d b : ι → A)
    (hdd : ∀ i j, quadraticAnticommutator (d i) (d j) = 0)
    (hbb : ∀ i j, quadraticAnticommutator (b i) (b j) = 0)
    (hdb : ∀ i j, quadraticAnticommutator (d i) (b j) =
      if i = j then -1 else 0) (i j l m : ι) :
    quadraticCommutator (-(d i * b j)) (-(d l * b m)) =
      (if j = l then -(d i * b m) else 0) -
        (if m = i then -(d l * b j) else 0) := by
  have hbd : quadraticAnticommutator (b j) (d l) =
      if j = l then -1 else 0 := by
    simpa only [quadraticAnticommutator, add_comm, eq_comm] using hdb l j
  have hn (x y : A) : quadraticCommutator (-x) (-y) = quadraticCommutator x y := by
    simp [quadraticCommutator]
  rw [hn, quadratic_commutator_expansion, hbd, hbb, hdd, hdb]
  by_cases hjl : j = l <;> by_cases him : i = m <;>
    simp [hjl, him, eq_comm]

/-- Signed CAR bilinears act on the forward family at the matching right index. -/
theorem negative_car_bilinear_action_forward {ι : Type*} [DecidableEq ι]
    (d b : ι → A)
    (hdd : ∀ i j, quadraticAnticommutator (d i) (d j) = 0)
    (hdb : ∀ i j, quadraticAnticommutator (d i) (b j) =
      if i = j then -1 else 0) (i j k : ι) :
    quadraticCommutator (-(d i * b j)) (d k) =
      if j = k then d i else 0 := by
  have hbd : quadraticAnticommutator (b j) (d k) =
      if j = k then -1 else 0 := by
    simpa only [quadraticAnticommutator, add_comm, eq_comm] using hdb k j
  calc
    _ = -(d i * quadraticAnticommutator (b j) (d k)) +
        quadraticAnticommutator (d i) (d k) * b j := by
      dsimp [quadraticCommutator, quadraticAnticommutator]
      noncomm_ring
    _ = _ := by
      rw [hbd, hdd]
      by_cases hjk : j = k <;> simp [hjk]

/-- Signed CAR bilinears act contragrediently on the backward family. -/
theorem negative_car_bilinear_action_backward {ι : Type*} [DecidableEq ι]
    (d b : ι → A)
    (hbb : ∀ i j, quadraticAnticommutator (b i) (b j) = 0)
    (hdb : ∀ i j, quadraticAnticommutator (d i) (b j) =
      if i = j then -1 else 0) (i j k : ι) :
    quadraticCommutator (-(d i * b j)) (b k) =
      if i = k then -(b j) else 0 := by
  calc
    _ = -(d i * quadraticAnticommutator (b j) (b k)) +
        quadraticAnticommutator (d i) (b k) * b j := by
      dsimp [quadraticCommutator, quadraticAnticommutator]
      noncomm_ring
    _ = _ := by
      rw [hbb, hdb]
      by_cases hik : i = k <;> simp [hik]

theorem commutator_sub_central (x y c : A) (hc : ∀ z : A, c * z = z * c) :
    x * y - y * x = (x - c) * (y - c) - (y - c) * (x - c) := by
  symm
  calc
    (x - c) * (y - c) - (y - c) * (x - c) =
        x * y - y * x + (y * c - c * y) + (c * x - x * c) := by
          noncomm_ring
    _ = x * y - y * x := by
      rw [hc y, hc x]
      simp

end

end InfoGeometry.OperatorAlgebra
