/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.Core.IdempotentGraphGrassmannian

/-!
# Ordered logarithmic pullbacks for two Peirce unipotents

The derivative here is the ordinary commutator with P, not a square-zero
exterior differential. The resulting correction satisfies the idempotency
transport equation. The full matrix Maurer–Cartan cochain and its flatness
are separately owned by `OperatorAlgebra.MatrixMaurerCartan`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def leftCornerPullback (P A C : B) : B :=
  ((1 + coneMinus P C) * (1 - conePlus P A)) *
    comm P ((1 + conePlus P A) * (1 - coneMinus P C))

def rightCornerPullback (P A C : B) : B :=
  comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
    ((1 + coneMinus P C) * (1 - conePlus P A))

variable {P : B} (hP : P * P = P) (A C : B)
include hP

theorem mixed_unipotent_commutator :
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) = genPhi P A C := by
  peirce_nf hP

theorem leftCornerPullback_eq :
    leftCornerPullback P A C = genPhi P A C - genSig P A C -
      genV P A C * coneMinus P C := by
  simp only [leftCornerPullback]
  peirce_nf hP

theorem rightCornerPullback_eq :
    rightCornerPullback P A C = genPhi P A C + genSig P A C -
      genV P A C * conePlus P A := by
  simp only [rightCornerPullback]
  peirce_nf hP

theorem cornerPullback_sum :
    rightCornerPullback P A C + leftCornerPullback P A C =
      (2 : ℤ) • genPhi P A C - genV P A C * genPhi P A C := by
  rw [rightCornerPullback_eq hP, leftCornerPullback_eq hP]
  peirce_nf hP

theorem cornerPullback_difference :
    rightCornerPullback P A C - leftCornerPullback P A C =
      (2 : ℤ) • genSig P A C - genV P A C * genJ P A C := by
  rw [rightCornerPullback_eq hP, leftCornerPullback_eq hP]
  peirce_nf hP

/-- The correction transports an idempotent; this is not dΩ + Ω² = 0. -/
theorem leftCornerPullback_idempotency :
    InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect
      (P + leftCornerPullback P A C) = 0 := by
  rw [leftCornerPullback_eq hP]
  simp only [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect]
  peirce_nf hP

/-- Exact characteristic-free equation for the transported-idempotent correction. -/
theorem leftCornerPullback_equation :
    anticomm P (leftCornerPullback P A C) - leftCornerPullback P A C +
      leftCornerPullback P A C * leftCornerPullback P A C = 0 := by
  have h := leftCornerPullback_idempotency hP A C
  simp only [InfoGeometry.Core.IdempotentGraphGrassmannian.idempotencyDefect,
    add_mul, mul_add, hP] at h
  simp only [anticomm]
  convert h using 1 <;> abel

end InfoGeometry.OperatorAlgebra.PeirceSpine
