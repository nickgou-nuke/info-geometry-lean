/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- Test -/
import Mathlib.Basic.Real.Basic

universe u

structure HurewiczFibration where
  hBase : Type u
  hTotal : Type u
  hProjection : hTotal → hBase

def hasPathLifting (F : HurewiczFibration) : Prop :=
  ∀ (γ : ℝ → F.hBase) (e : F.hTotal),
    F.hProjection e = γ 0 → True
