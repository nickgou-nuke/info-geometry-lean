/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Ring.Basic

/-!
# Algebraic Commutants of Operator Sets

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * The commutant of a set of module endomorphisms `A : Set (Module.End R M)` consists of all
    endomorphisms `y : Module.End R M` that commute with every `x ∈ A`.
- BUCKET 2 (Shared Algebraic Carrier):
  * Provides the canonical `Commutant` definition used across the modular-conjugation and
    Souriau–Tomita modules without wrapper structures.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `mem_commutant_iff`: explicit bidirectional characterization of membership in `Commutant A`
    via pointwise commutation `∀ x ∈ A, x * y = y * x`.
-/

namespace InfoGeometry.GrandUnification

variable {R M : Type*} [Ring R] [AddCommMonoid M] [Module R M]

/-- The commutant of a set of module endomorphisms. -/
def Commutant (A : Set (Module.End R M)) : Set (Module.End R M) :=
  {y | ∀ x ∈ A, x * y = y * x}

/-- Membership in a commutant is equivalent to pointwise commutation with its set. -/
theorem mem_commutant_iff (A : Set (Module.End R M)) (y : Module.End R M) :
    y ∈ Commutant A ↔ ∀ x ∈ A, x * y = y * x := by
  constructor
  · intro hy x hx
    exact hy x hx
  · intro hy x hx
    exact hy x hx

end InfoGeometry.GrandUnification
