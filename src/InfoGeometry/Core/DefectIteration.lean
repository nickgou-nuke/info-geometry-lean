/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceDefect
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic

/-!
# Finite iteration of the idempotency defect

Iterates preserve centralizers and split across mutually annihilating summands.
Their generated subalgebras form an antitone chain in the native subalgebra
partial order. The ambient algebra remains unrestricted and noncommutative;
the chain need not be strict and does not assert new adjoint weights.
-/

namespace InfoGeometry.Core.DefectIteration

open IdempotencyDefect

variable {A B : Type*} [Ring A] [Ring B]

theorem commute_defect {a x : A} (h : Commute a x) :
    Commute a (defect x) :=
  (h.mul_right h).sub_right h

theorem commute_iterate {a x : A} (h : Commute a x) (n : ℕ) :
    Commute a (defect^[n] x) := by
  induction n with
  | zero => simpa only [Function.iterate_zero_apply] using h
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact commute_defect ih

theorem iterate_mul_eq_zero {x y : A} (hxy : x * y = 0) (n : ℕ) :
    (defect^[n] x) * y = 0 := by
  induction n with
  | zero => simpa only [Function.iterate_zero_apply] using hxy
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact defect_mul_eq_zero ih

theorem mul_iterate_eq_zero {x y : A} (hxy : x * y = 0) (n : ℕ) :
    x * (defect^[n] y) = 0 := by
  induction n with
  | zero => simpa only [Function.iterate_zero_apply] using hxy
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact mul_defect_eq_zero ih

/-- The two iteration counts are independent. -/
theorem iterate_mul_iterate_eq_zero {x y : A} (hxy : x * y = 0) (m n : ℕ) :
    (defect^[m] x) * (defect^[n] y) = 0 :=
  iterate_mul_eq_zero (mul_iterate_eq_zero hxy n) m

theorem iterate_add_of_mul_eq_zero {x y : A}
    (hxy : x * y = 0) (hyx : y * x = 0) (n : ℕ) :
    defect^[n] (x + y) = defect^[n] x + defect^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', ih]
      exact defect_add_of_mul_eq_zero
        (iterate_mul_iterate_eq_zero hxy n n)
        (iterate_mul_iterate_eq_zero hyx n n)

theorem map_iterate (f : A →+* B) (x : A) (n : ℕ) :
    f (defect^[n] x) = defect^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', map_defect, ih]

/-- The first tangent step enters the centralizer, which contains every later step. -/
theorem commute_iterate_add_idempotent {p y : A} (hp : IsIdempotentElem p)
    (hy : p * y + y * p = y) (n : ℕ) :
    Commute p (defect^[n + 1] (p + y)) := by
  rw [Function.iterate_succ_apply, PeirceDefect.defect_add_idempotent_eq_square hp hy]
  exact commute_iterate (PeirceDefect.commute_square_of_tangent hp hy) n

section Subalgebra

variable (R : Type*) [CommRing R] [Algebra R A]

theorem iterate_mem_subalgebra (S : Subalgebra R A) {x : A}
    (hx : x ∈ S) (n : ℕ) : defect^[n] x ∈ S := by
  induction n with
  | zero => simpa only [Function.iterate_zero_apply] using hx
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact S.sub_mem (S.mul_mem ih ih) ih

theorem iterate_mem_adjoin (x : A) (n : ℕ) :
    defect^[n] x ∈ Algebra.adjoin R ({x} : Set A) :=
  iterate_mem_subalgebra R _ (Algebra.self_mem_adjoin_singleton R x) n

/-- Taking the defect can lose generated operators; it cannot enlarge their algebra. -/
theorem adjoin_defect_le (x : A) :
    Algebra.adjoin R ({defect x} : Set A) ≤ Algebra.adjoin R ({x} : Set A) := by
  apply Algebra.adjoin_singleton_le
  exact (Algebra.adjoin R ({x} : Set A)).sub_mem
    ((Algebra.adjoin R ({x} : Set A)).mul_mem
      (Algebra.self_mem_adjoin_singleton R x) (Algebra.self_mem_adjoin_singleton R x))
    (Algebra.self_mem_adjoin_singleton R x)

/-- A genuine order statement on native subalgebras, with no strictness assumption. -/
theorem adjoin_iterate_antitone (x : A) :
    Antitone (fun n : ℕ => Algebra.adjoin R ({defect^[n] x} : Set A)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [Function.iterate_succ_apply']
  exact adjoin_defect_le R (defect^[n] x)

end Subalgebra

end InfoGeometry.Core.DefectIteration
