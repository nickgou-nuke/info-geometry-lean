/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- ProgressiveSpan.lean
-- Definitions for progressive point‑span `x ∧ y` used throughout the Plücker‑Grassmann constructions.

import Mathlib.LinearAlgebra.Exterior
import Mathlib.Data.Matrix.Notation

open scoped ExteriorAlgebra

namespace InfoGeometry.Canonical

/-- The exterior product of two vectors in a module `V` over a commutative ring `R`.
    This is the basic `∧` operation used for Plücker coordinates.
-/
def pointSpan {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (x y : V) : ExteriorAlgebra R V := ⟪x, y⟫

-- Lemma: `pointSpan` is alternating.
@[simp] lemma pointSpan_eq_zero_of_eq {R V} [CommRing R] [AddCommGroup V] [Module R V]
    (x : V) : pointSpan x x = 0 := by
  unfold pointSpan
  simp

end InfoGeometry.Canonical
