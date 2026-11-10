/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- In any non-commutative ring `[Ring B]`, if `u` is an involution (`u * u = 1`) that anticommutes
with `x` (`u * x = -(x * u)`) and `y` (`u * y = -(y * u)`), then `u` commutes with `x * y` (`u * (x * y) = (x * y) * u`). -/
theorem ring_even_sector_closure_commute
    {B : Type*} [Ring B] (u x y : B)
    (hx : u * x = -(x * u)) (hy : u * y = -(y * u)) :
    u * (x * y) = (x * y) * u := by
  calc
    u * (x * y) = (u * x) * y := by rw [mul_assoc]
    _ = -(x * u) * y := by rw [hx]
    _ = -(x * (u * y)) := by rw [neg_mul, mul_assoc]
    _ = -(x * -(y * u)) := by rw [hy]
    _ = (x * y) * u := by rw [mul_neg, neg_neg, mul_assoc]

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Четният сектор (The Operator Algebra) -/
abbrev ClPlus := evenOdd Q 0

/-- Нечетният сектор (The Spacetime Bimodule) -/
abbrev ClMinus := evenOdd Q 1

/-- ТЕОРЕМА 1: Четен * Четен = Четен (Subalgebra Closure) -/
theorem clPlus_mul_clPlus (a b : CliffordAlgebra Q)
    (ha : a ∈ ClPlus Q) (hb : b ∈ ClPlus Q) :
    a * b ∈ ClPlus Q := by
  have h_mul := Submodule.mul_mem_mul ha hb
  have h_le := evenOdd_mul_le Q 0 0 h_mul
  rwa [add_zero] at h_le

/-- ТЕОРЕМА 2: Четен * Нечетен = Нечетен (Left Module Action) -/
theorem clPlus_mul_clMinus (a b : CliffordAlgebra Q)
    (ha : a ∈ ClPlus Q) (hb : b ∈ ClMinus Q) :
    a * b ∈ ClMinus Q := by
  have h_mul := Submodule.mul_mem_mul ha hb
  have h_le := evenOdd_mul_le Q 0 1 h_mul
  rwa [zero_add] at h_le

/-- ТЕОРЕМА 3: Нечетен * Четен = Нечетен (Right Module Action) -/
theorem clMinus_mul_clPlus (a b : CliffordAlgebra Q)
    (ha : a ∈ ClMinus Q) (hb : b ∈ ClPlus Q) :
    a * b ∈ ClMinus Q := by
  have h_mul := Submodule.mul_mem_mul ha hb
  have h_le := evenOdd_mul_le Q 1 0 h_mul
  rwa [add_zero] at h_le

/-- ТЕОРЕМА 4: Нечетен * Нечетен = Четен (The Vector Inner Product returns to operators) -/
theorem clMinus_mul_clMinus (a b : CliffordAlgebra Q)
    (ha : a ∈ ClMinus Q) (hb : b ∈ ClMinus Q) :
    a * b ∈ ClPlus Q := by
  have h_mul := Submodule.mul_mem_mul ha hb
  have h_le := evenOdd_mul_le Q 1 1 h_mul
  have h_add : (1 : ZMod 2) + (1 : ZMod 2) = 0 := by decide
  rwa [h_add] at h_le

end InfoGeometry.Clifford.Hestenes
