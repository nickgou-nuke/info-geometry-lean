/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace InfoGeometry.Physics.TimeReversal

universe u v

/-- Time-reversal operator structure -/
structure TrSymmetry (ι : Type u) (B : Type v) [Fintype ι] [DecidableEq ι] [Ring B] where
  T : Matrix ι ι B
  hT_sq : T * T = -(1 : Matrix ι ι B)
  hT_skew : T.transpose = -T

/-- Theorem: Time-reversal square law -/
lemma time_reversal_square {ι : Type u} {B : Type v} [Fintype ι] [DecidableEq ι] [Ring B]
    (ts : TrSymmetry ι B) :
    ts.T * ts.T = -(1 : Matrix ι ι B) := by
  exact ts.hT_sq

/-- Theorem: Time-reversal skew-symmetry -/
theorem time_reversal_skew {ι : Type u} {B : Type v} [Fintype ι] [DecidableEq ι] [Ring B]
    (ts : TrSymmetry ι B) :
    ts.T.transpose = -ts.T := by
  exact ts.hT_skew

end InfoGeometry.Physics.TimeReversal
