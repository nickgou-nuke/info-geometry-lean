/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.NoncommRing

/-!
# The algebraic first jet of inner conjugation

On Mathlib's dual numbers over any noncommutative ring, `1 + ε G` is an actual
unit. Its action on `X + ε Y` is exactly `X + ε (Y + [G,X])`.
No topology, limiting argument, or exponential convergence is involved.
-/

namespace InfoGeometry.Core.InnerConjugationJet

open TrivSqZeroExt

variable {A : Type*} [Ring A]

/-- The first-order exponential, with its genuine inverse in the dual ring. -/
def unit (G : A) : (DualNumber A)ˣ where
  val := inl 1 + inr G
  inv := inl 1 - inr G
  val_inv := by ext <;> simp
  inv_val := by ext <;> simp

/-- Exact first-order transport, including an existing tangent component. -/
theorem conjugate (G X Y : A) :
    (unit G : DualNumber A) * (inl X + inr Y) * (↑(unit G)⁻¹ : DualNumber A) =
      inl X + inr (Y + (G * X - X * G)) := by
  ext <;> simp [unit]; noncomm_ring

end InfoGeometry.Core.InnerConjugationJet
