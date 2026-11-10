/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- Test -/
import Mathlib.Basic.Real.Basic

universe u

structure SetMap where
  base : Type u
  total : Type u
  projection : total → base

/-! Set-theoretic path lifting only: this carrier has no topology, so
continuity of the base path or lift is not part of this predicate. -/
def hasSetTheoreticPathLifting (F : SetMap) : Prop :=
  ∀ (γ : ℝ → F.base) (e : F.total),
    F.projection e = γ 0 →
      ∃ lift : ℝ → F.total,
        lift 0 = e ∧ ∀ t, F.projection (lift t) = γ t
