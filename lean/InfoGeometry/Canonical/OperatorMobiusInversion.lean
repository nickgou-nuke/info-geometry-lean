/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import InfoGeometry.Cantor.CliffordMarkovOperators

/-!
# Möbius inversion with noncommutative operator coefficients

The divisor-zeta transform and its Möbius inverse apply to functions valued
in any ring, including a genuinely noncommutative endomorphism ring. The
arithmetic Möbius coefficients act on the left; no reordering of operator
products or commutativity hypothesis is used. The finite Cantor specialization
uses the represented split-Clifford Fock operators as its carrier.

Dependency order: divisor-zeta transform → Möbius inversion → represented
Fock-operator instance. The Riemann-zeta Dirichlet-series identity and
operator-valued resolvent identities are separate analytic/algebraic branches;
this file asserts no bridge between them.
-/

noncomputable section

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open BigOperators

namespace InfoGeometry.Canonical.OperatorMobiusInversion

/-- The divisor-zeta transform of an operator-valued arithmetic function. -/
def divisorZetaTransform {A : Type*} [Ring A] (f : ℕ → A) (n : ℕ) : A :=
  ∑ d ∈ n.divisors, f d

/-- The ordered Möbius transform of an operator-valued arithmetic function.
The integer Möbius coefficient acts on the left of the operator value. -/
def divisorMobiusTransform {A : Type*} [Ring A] (g : ℕ → A) (n : ℕ) : A :=
  ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : A) * g x.snd

/-- Möbius inversion for operator-valued arithmetic functions. This is valid
for noncommutative rings, so values may be genuine operators and are never
commuted in the proof. -/
theorem divisorZetaTransform_eq_iff_mobius_recovers
    {A : Type*} [Ring A] (f g : ℕ → A) :
    (∀ n > 0, divisorZetaTransform f n = g n) ↔
      ∀ n > 0, divisorMobiusTransform g n = f n := by
  exact sum_eq_iff_sum_mul_moebius_eq

open InfoGeometry.Cantor.CliffordMarkovOperators
open InfoGeometry.Clifford.ClNNFockRepresentation
open InfoGeometry.Clifford.FockSpaceCAR

/-- Möbius inversion on the actual endomorphism ring of the finite Cantor
split-Clifford Fock module. The sequence entries are arbitrary operators; in
particular, the theorem does not assume they are diagonal or pairwise commute. -/
theorem cantorFock_divisorZeta_eq_iff_mobius_recovers
    (n : ℕ)
    (f g : ℕ → Module.End ℝ (FockSpace (PrimalSheet n))) :
    (∀ m > 0, divisorZetaTransform f m = g m) ↔
      ∀ m > 0, divisorMobiusTransform g m = f m := by
  exact divisorZetaTransform_eq_iff_mobius_recovers f g

end InfoGeometry.Canonical.OperatorMobiusInversion
