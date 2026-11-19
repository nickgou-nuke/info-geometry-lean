/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
// PolarForm.lean
-- Bilinear polar form linking point‑ray and plane‑axis coordinates.

import Mathlib.Data.Matrix.Notation
import Mathlib.Algebra.Algebra.Basic

open Matrix

namespace InfoGeometry.Canonical

/-- Given two 4‑vectors `p` and `q` representing Plücker coordinates, the polar form is
    the bilinear expression:
    `p₀₁*q₂₃ - p₀₂*q₁₃ + p₀₃*q₁₂ + p₁₂*q₀₃ - p₁₃*q₀₂ + p₂₃*q₀₁`.
    This matches the definition used in the AI‑Studio transcript.
-/

def polar (p q : Fin 4 → ℤ) : ℤ :=
  p 0 * q 3 - p 1 * q 2 + p 2 * q 1 + p 3 * q 0 - p 0 * q 2 + p 1 * q 3

@[simp] lemma polar_swap (p q : Fin 4 → ℤ) : polar p q = - polar q p := by
  unfold polar
  ring

end InfoGeometry.Canonical
