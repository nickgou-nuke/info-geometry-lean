/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

/-!
# Adjoint transport for the native doubled-space matrix action

The canonical `2 × 2` real matrix action on `DoubledSpace E` transports the
matrix transpose to the Hilbert adjoint.  This is the real operator transport
law needed by the doubled-Krein matrix bridge.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- The Hilbert adjoint of the native doubled-space action is represented by
matrix transpose. -/
theorem ρclock_adjoint_transpose
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ContinuousLinearMap.adjoint (ρclock (E := E) A) =
      ρclock (E := E) A.transpose := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := ρclock (E := E) A.transpose)
    (B := ρclock (E := E) A)).2 ?_
  intro u v
  change
    inner ℝ (A 0 0 • WithLp.fst u + A 1 0 • WithLp.snd u) (WithLp.fst v) +
      inner ℝ (A 0 1 • WithLp.fst u + A 1 1 • WithLp.snd u) (WithLp.snd v) =
    inner ℝ (WithLp.fst u) (A 0 0 • WithLp.fst v + A 0 1 • WithLp.snd v) +
      inner ℝ (WithLp.snd u) (A 1 0 • WithLp.fst v + A 1 1 • WithLp.snd v)
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  ring_nf

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_adjoint_transpose
