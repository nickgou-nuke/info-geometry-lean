/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

namespace InfoGeometry.Physics.TimeReversal
open scoped Matrix

universe u

/-- Time-reversal operator structure -/
structure TrSymmetry (B : Type u) [Ring B] (n : ℕ) where
  T : Matrix (Fin n) (Fin n) B
  hT_sq : T * T = -1
  hT_skew : Tᵀ = -T

/-- Theorem: Time-reversal square law -/
lemma time_reversal_square {B : Type u} [Ring B] {n : ℕ} (ts : TrSymmetry B n) :
    ts.T * ts.T = -1 := by
  exact ts.hT_sq

/-- Theorem: Time-reversal skew-symmetry -/
theorem time_reversal_skew {B : Type u} [Ring B] {n : ℕ} (ts : TrSymmetry B n) :
    ts.Tᵀ = -ts.T := by
  exact ts.hT_skew

end InfoGeometry.Physics.TimeReversal
