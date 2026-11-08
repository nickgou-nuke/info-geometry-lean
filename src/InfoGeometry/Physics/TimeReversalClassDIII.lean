/- Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic

namespace InfoGeometry.Physics.TimeReversal

universe u

/-- Time-reversal operator structure -/
structure TrSymmetry (B : Type u) [Ring B] where
  T : B
  hT_sq : T * T = -1
  hT_skew : Tᵀ = -T

/-- Theorem: Time-reversal square law -/
lemma time_reversal_square {B : Type u} [Ring B] (ts : TrSymmetry B) :
    ts.T * ts.T = -1 := by
  exact ts.hT_sq

/-- Theorem: Time-reversal skew-symmetry -/
theorem time_reversal_skew {B : Type u} [Ring B] (ts : TrSymmetry B) :
    ts.Tᵀ = -ts.T := by
  exact ts.hT_skew

end InfoGeometry.Physics.TimeReversal
