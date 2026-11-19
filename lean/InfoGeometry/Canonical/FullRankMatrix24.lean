/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
-- FullRankMatrix24.lean
-- Definition and basic lemmas for a 2×4 matrix of full rank used in Plücker coordinates.

import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix
import Mathlib.LinearAlgebra.Rank

open Matrix

namespace InfoGeometry.Canonical

/-- A 2×4 matrix over a commutative ring `R`. -/
abbrev Matrix2x4 (R : Type*) [CommRing R] := Matrix (Fin 2) (Fin 4) R

/-- Predicate that a 2×4 matrix has full rank (i.e., rank = 2). -/

def FullRankMatrix24 (R : Type*) [CommRing R] (M : Matrix2x4 R) : Prop :=
  Matrix.rank M = 2

-- Basic lemmas (placeholders for later proofs).

@[simp] lemma fullRank_of_eq_one {R} [CommRing R] {M : Matrix2x4 R} (h : Matrix.rank M = 1) : ¬ FullRankMatrix24 R M := by
  intro hf
  have := hf
  dsimp [FullRankMatrix24] at hf
  have : (Matrix.rank M) = 2 := hf
  omega

-- TODO: add lemmas about transformation under GL₂ actions etc.

end InfoGeometry.Canonical
