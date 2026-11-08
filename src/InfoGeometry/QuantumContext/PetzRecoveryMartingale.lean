/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic

/-!
# Algebraic support compression on noncommutative rings

The compression `X ↦ P * X * P` is idempotent when `P` is idempotent. If
`P * Q = 0`, it annihilates the corner `Q * Y * Q`. These ring identities are
used by the full-matrix Markov range-projection owner. This module does not
assert a state-dependent Petz recovery theorem, a probability martingale, a
Connes cocycle, or a Jones index.
-/

namespace InfoGeometry.QuantumContext.PetzMartingale

variable {R : Type*} [Ring R]

/-- Algebraic compression by an idempotent, `X ↦ P * X * P`. -/
def petzRecovery (P : R) (X : R) : R := P * X * P

/-- Compression by an idempotent is idempotent on the ambient ring. -/
theorem petz_recovery_idempotent (P : R) (hP : P * P = P) (X : R) :
    petzRecovery P (petzRecovery P X) = petzRecovery P X := by
  dsimp [petzRecovery]
  calc
    P * (P * X * P) * P = (P * P) * X * (P * P) := by
      repeat rw [mul_assoc]
    _ = P * X * P := by rw [hP]

end InfoGeometry.QuantumContext.PetzMartingale
