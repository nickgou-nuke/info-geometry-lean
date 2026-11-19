/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Two-level thermal stationarity over a noncommutative coefficient ring

All operator entries, transition rates, and Gibbs weights in this file lie in
an arbitrary associative ring `B`. The carrier is the full matrix algebra
`Matrix (Fin 2) (Fin 2) B`; products are ordered and no commutativity of `B` is
assumed. The algebraic transition defect is division-free. Its uniqueness
statement explicitly assumes the cancellations needed over a general ring.

This is an algebraic finite-matrix result. It does not define exponentials,
operator logarithms, positivity, a continuous-time semigroup, or quantum
relative entropy; those require additional analytic and ordered structure on
`B` and a specified trace/state functional.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.PeirceBiSandwich

/-- Full two-sheet operator carrier over the possibly noncommutative ring `B`. -/
abbrev TwoSheetOperator (B : Type*) := Matrix (Fin 2) (Fin 2) B

/-- Division-free twice-scaled two-rate transition defect. Rate operators act
on the left, and the displayed order is part of the definition. -/
def twoRateTransitionDefect2 {B : Type*} [Ring B]
    (γup γdown : B) (ρ : TwoSheetOperator B) : TwoSheetOperator B :=
  !![2 * (-(γdown * ρ 0 0) + γup * ρ 1 1), -(γdown + γup) * ρ 0 1;
    -(γdown + γup) * ρ 1 0, 2 * (γdown * ρ 0 0 - γup * ρ 1 1)]

/-- A diagonal two-sheet operator with arbitrary noncommuting coefficients. -/
def twoSheetDiagonalOperator {B : Type*} [Ring B] (p q : B) : TwoSheetOperator B :=
  !![p, 0; 0, q]

/-- Detailed balance makes the diagonal operator stationary for the
division-free two-rate transition defect; no normalization is needed for
stationarity itself. -/
theorem twoSheetDiagonalOperator_stationary {B : Type*} [Ring B]
    (γup γdown p q : B) (h_balance : γdown * p = γup * q) :
    twoRateTransitionDefect2 γup γdown (twoSheetDiagonalOperator p q) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoRateTransitionDefect2, twoSheetDiagonalOperator, h_balance]

/-- Uniqueness of a normalized stationary two-sheet operator. The assumptions
`h_two_cancel` and `h_total_inv` are explicit because cancellation by two and
invertibility of the total transition rate are not valid in every ring. -/
theorem twoRateTransitionDefect2_unique_stationary {B : Type*} [Ring B]
    (γup γdown p q totalInv : B) (ρ : TwoSheetOperator B)
    (h_balance : γdown * p = γup * q) (h_normalized : p + q = 1)
    (h_trace : ρ 0 0 + ρ 1 1 = 1)
    (h_two_cancel : ∀ z : B, (2 : B) * z = 0 → z = 0)
    (h_total_inv : totalInv * (γdown + γup) = 1)
    (h_stationary : twoRateTransitionDefect2 γup γdown ρ = 0) :
    ρ = twoSheetDiagonalOperator p q := by
  have h00two : (2 : B) * (-(γdown * ρ 0 0) + γup * ρ 1 1) = 0 := by
    have h := congrArg (fun M : TwoSheetOperator B => M 0 0) h_stationary
    simpa [twoRateTransitionDefect2] using h
  have h00 : -(γdown * ρ 0 0) + γup * ρ 1 1 = 0 :=
    h_two_cancel _ h00two
  have h01 : (γdown + γup) * ρ 0 1 = 0 := by
    have h := congrArg (fun M : TwoSheetOperator B => M 0 1) h_stationary
    have hcoef : (-(γdown + γup)) * (ρ 0 1) = 0 := by
      simpa [twoRateTransitionDefect2] using h
    have hneg : -((γdown + γup) * (ρ 0 1)) = 0 := by
      simpa only [neg_mul] using hcoef
    exact neg_eq_zero.mp hneg
  have h10 : (γdown + γup) * ρ 1 0 = 0 := by
    have h := congrArg (fun M : TwoSheetOperator B => M 1 0) h_stationary
    have hcoef : (-(γdown + γup)) * (ρ 1 0) = 0 := by
      simpa [twoRateTransitionDefect2] using h
    have hneg : -((γdown + γup) * (ρ 1 0)) = 0 := by
      simpa only [neg_mul] using hcoef
    exact neg_eq_zero.mp hneg
  have h01zero : ρ 0 1 = 0 := by
    calc
      ρ 0 1 = 1 * ρ 0 1 := by rw [one_mul]
      _ = (totalInv * (γdown + γup)) * ρ 0 1 := by rw [h_total_inv]
      _ = totalInv * ((γdown + γup) * ρ 0 1) := by rw [mul_assoc]
      _ = 0 := by rw [h01, mul_zero]
  have h10zero : ρ 1 0 = 0 := by
    calc
      ρ 1 0 = 1 * ρ 1 0 := by rw [one_mul]
      _ = (totalInv * (γdown + γup)) * ρ 1 0 := by rw [h_total_inv]
      _ = totalInv * ((γdown + γup) * ρ 1 0) := by rw [mul_assoc]
      _ = 0 := by rw [h10, mul_zero]
  have h_rate : γdown * ρ 0 0 = γup * ρ 1 1 := by
    calc
      γdown * ρ 0 0 = γdown * ρ 0 0 + (-(γdown * ρ 0 0) + γup * ρ 1 1) := by
        rw [h00, add_zero]
      _ = γup * ρ 1 1 := by abel
  have h_total_q : (γdown + γup) * ρ 1 1 = γdown := by
    calc
      (γdown + γup) * ρ 1 1 = γdown * ρ 1 1 + γup * ρ 1 1 := by rw [add_mul]
      _ = γdown * ρ 1 1 + γdown * ρ 0 0 := by rw [← h_rate]
      _ = γdown * (ρ 1 1 + ρ 0 0) := by rw [mul_add]
      _ = γdown * (ρ 0 0 + ρ 1 1) := by rw [add_comm]
      _ = γdown := by rw [h_trace, mul_one]
  have h_q : ρ 1 1 = totalInv * γdown := by
    calc
      ρ 1 1 = 1 * ρ 1 1 := by rw [one_mul]
      _ = (totalInv * (γdown + γup)) * ρ 1 1 := by rw [h_total_inv]
      _ = totalInv * ((γdown + γup) * ρ 1 1) := by rw [mul_assoc]
      _ = totalInv * γdown := by rw [h_total_q]
  have h_total_q_gibbs : (γdown + γup) * q = γdown := by
    calc
      (γdown + γup) * q = γdown * q + γup * q := by rw [add_mul]
      _ = γdown * q + γdown * p := by rw [← h_balance]
      _ = γdown * (q + p) := by rw [mul_add]
      _ = γdown * (p + q) := by rw [add_comm]
      _ = γdown := by rw [h_normalized, mul_one]
  have hq : q = totalInv * γdown := by
    calc
      q = 1 * q := by rw [one_mul]
      _ = (totalInv * (γdown + γup)) * q := by rw [h_total_inv]
      _ = totalInv * ((γdown + γup) * q) := by rw [mul_assoc]
      _ = totalInv * γdown := by rw [h_total_q_gibbs]
  have hp : ρ 0 0 = p := by
    have hp_sum : ρ 0 0 + ρ 1 1 = p + q := by rw [h_trace, h_normalized]
    rw [h_q, hq] at hp_sum
    exact add_right_cancel hp_sum
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [twoSheetDiagonalOperator] using hp
  · simp [twoSheetDiagonalOperator, h01zero]
  · simp [twoSheetDiagonalOperator, h10zero]
  · simpa [twoSheetDiagonalOperator] using h_q.trans hq.symm

end InfoGeometry.OperatorAlgebra.PeirceBiSandwich
