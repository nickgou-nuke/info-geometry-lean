/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
import InfoGeometry.Krein.DoubledSpaceMatrixAdjointTransposeWave93
import InfoGeometry.Krein.KreinSpace

/-!
# Krein-adjoint transport for the native doubled-space matrix action

The native real `2 × 2` action transports the fundamental-symmetry adjoint to
matrix transpose conjugated by the diagonal Krein-sign matrix.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- The native Krein adjoint of a represented matrix is represented by the
matrix Krein adjoint `ε Aᵀ ε`. -/
theorem ρclock_kreinAdjoint
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    KreinSpace.kreinAdjoint (H := DoubledSpace E) (ρclock (E := E) A) =
      ρclock (E := E) (matrixEpsilon * A.transpose * matrixEpsilon) := by
  have hε :
      KreinSpace.jCLM (H := DoubledSpace E) = spectral_epsilon (E := E) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> rfl
  rw [KreinSpace.kreinAdjoint, hε, ρclock_adjoint_transpose]
  rw [← ρclock_matrixEpsilon (E := E)]
  rw [← ρclock_mul, ← ρclock_mul]
  simp [mul_assoc]

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_kreinAdjoint
