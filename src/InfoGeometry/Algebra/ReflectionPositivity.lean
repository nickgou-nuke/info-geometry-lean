/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.SquareZeroSandwich
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Algebraic reflection positivity

This file records a reflection and a conditional reflection-positive
functional. The ordered codomain and positive subalgebra are explicit inputs;
this algebraic interface does not construct a C*-algebra, a state space, a
Hilbert-space reconstruction, or a tensor product of states.
-/

namespace InfoGeometry.Algebra.ReflectionPositivity

/-! A star-compatible, involutive anti-automorphism. -/
structure Reflection (A : Type*) [Ring A] [StarRing A] where
  theta : A → A
  h_theta_involutive : ∀ x, theta (theta x) = x
  h_theta_anti_mul : ∀ x y, theta (x * y) = theta y * theta x
  h_theta_star : ∀ x, theta (Star.star x) = Star.star (theta x)

/-! A real-valued additive functional with reflection positivity on `Aplus`.
The positivity condition is a genuine order proposition in `R`. -/
structure ReflectionPositiveState (A R : Type*) [Ring A] [StarRing A]
    [Ring R] [LinearOrder R] [IsOrderedRing R]
    (theta : Reflection A) (Aplus : Set A) where
  omega : A → R
  map_add : ∀ x y, omega (x + y) = omega x + omega y
  map_zsmul : ∀ (n : ℤ) (x : A), omega (n • x) = n • omega x
  positive : ∀ x, x ∈ Aplus → 0 ≤ omega (theta.theta x * x)

/-! The reflection form is valued in the ordered coefficient ring. -/
def reflectionForm {A R : Type*} [Ring A] [StarRing A]
    [Ring R] [LinearOrder R] [IsOrderedRing R]
    (theta : Reflection A) (omega : A → R)
    (a b : A) : R := omega (theta.theta a * b)

theorem reflection_form_positive {A R : Type*} [Ring A] [StarRing A]
    [Ring R] [LinearOrder R] [IsOrderedRing R]
    {theta : Reflection A} {Aplus : Set A}
    (state : ReflectionPositiveState A R theta Aplus) {a : A}
    (ha : a ∈ Aplus) : 0 ≤ reflectionForm theta state.omega a a := by
  exact state.positive a ha

theorem reflection_form_add_right {A R : Type*} [Ring A] [StarRing A]
    [Ring R] [LinearOrder R] [IsOrderedRing R]
    (theta : Reflection A) (omega : A → R)
    (a b c : A) (hω : ∀ x y, omega (x + y) = omega x + omega y) :
    reflectionForm theta omega a (b + c) =
      reflectionForm theta omega a b + reflectionForm theta omega a c := by
  simp only [reflectionForm, mul_add, hω]

theorem reflection_anti_mul {A : Type*} [Ring A] [StarRing A]
    (theta : Reflection A) (x y : A) :
    theta.theta (x * y) = theta.theta y * theta.theta x :=
  theta.h_theta_anti_mul x y

theorem reflection_involutive {A : Type*} [Ring A] [StarRing A]
    (theta : Reflection A) (x : A) : theta.theta (theta.theta x) = x :=
  theta.h_theta_involutive x

/-!
The former `InvertibleState` placeholder asserted `True` instead of defining
state stacking or a tensor product. The inverse-phase claim remains open until
such a carrier and its product-state law are supplied.
-/

end InfoGeometry.Algebra.ReflectionPositivity
