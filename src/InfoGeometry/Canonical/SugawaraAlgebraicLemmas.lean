/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Meta.Architecture

/-!
# Associative-Ring Commutator Identities for Sugawara Mode Sums

This module proves the associative-ring commutator identities (Leibniz derivation
rules and finite-sum distributivity) used in the Sugawara bilinear current calculus.

- BUCKET 1 (Real Math in This File):
- `comm`, `comm_mul_left`, `comm_mul_right`
- `comm_zero_right`, `zero_comm`, `comm_self`
- `comm_sum_left`, `comm_sum_right`

- BUCKET 2 (Meaningful Mathematical Results Used):
- `Mathlib.Tactic.NoncommRing`
- `Finset.sum_mul`, `Finset.mul_sum`, `Finset.sum_sub_distrib`

- BUCKET 3 (Excluded Wrapper Patterns):
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.SugawaraAlgebraicLemmas

variable {Op : Type*} [Ring Op]

/-- Associative-ring commutator $[A, B] = A B - B A$. -/
@[rep_depth operator]
def comm (A B : Op) : Op :=
  A * B - B * A

/-- Left product derivation law for the associative commutator:
`comm (A * B) C = A * comm B C + comm A C * B`. -/
@[rep_depth operator]
theorem comm_mul_left (A B C : Op) :
    comm (A * B) C = A * comm B C + comm A C * B := by
  unfold comm
  noncomm_ring

/-- Right product derivation law for the associative commutator:
`comm A (B * C) = comm A B * C + B * comm A C`. -/
@[rep_depth operator]
theorem comm_mul_right (A B C : Op) :
    comm A (B * C) = comm A B * C + B * comm A C := by
  unfold comm
  noncomm_ring

/-- The commutator of any ring element with `0` on the right vanishes. -/
@[rep_depth operator]
theorem comm_zero_right (A : Op) : comm A 0 = 0 := by
  unfold comm
  simp

/-- The commutator of `0` on the left with any ring element vanishes. -/
@[rep_depth operator]
theorem zero_comm (A : Op) : comm 0 A = 0 := by
  unfold comm
  simp

/-- The commutator of any ring element with itself vanishes. -/
@[rep_depth operator]
theorem comm_self (A : Op) : comm A A = 0 := by
  unfold comm
  simp

/-- The associative commutator distributes over a finite sum in its left argument. -/
@[rep_depth operator]
theorem comm_sum_left {ι : Type*} (s : Finset ι) (A : ι → Op) (B : Op) :
    comm (Finset.sum s A) B = Finset.sum s (fun i => comm (A i) B) := by
  unfold comm
  rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The associative commutator distributes over a finite sum in its right argument. -/
@[rep_depth operator]
theorem comm_sum_right {ι : Type*} (s : Finset ι) (A : Op) (B : ι → Op) :
    comm A (Finset.sum s B) = Finset.sum s (fun i => comm A (B i)) := by
  unfold comm
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

end InfoGeometry.Canonical.SugawaraAlgebraicLemmas
