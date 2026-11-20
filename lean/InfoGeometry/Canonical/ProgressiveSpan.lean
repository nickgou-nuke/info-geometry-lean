/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- ProgressiveSpan.lean
-- Definitions for progressive point‑span `x ∧ y` used throughout the Plücker‑Grassmann constructions.

import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

open scoped ExteriorAlgebra

namespace InfoGeometry.Canonical

/-- The exterior product of two vectors in a module `V` over a commutative ring `R`.
    This is the basic `∧` operation used for Plücker coordinates.
-/
def pointSpan {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]
    (x y : V) : ExteriorAlgebra R V :=
  ExteriorAlgebra.ι R x * ExteriorAlgebra.ι R y

-- Lemma: `pointSpan` is alternating.
@[simp] lemma pointSpan_eq_zero_of_eq {R : Type*} {V : Type*}
    [CommRing R] [AddCommGroup V] [Module R V] (x : V) :
    pointSpan (R := R) x x = 0 := by
  exact ExteriorAlgebra.ι_sq_zero x

end InfoGeometry.Canonical
