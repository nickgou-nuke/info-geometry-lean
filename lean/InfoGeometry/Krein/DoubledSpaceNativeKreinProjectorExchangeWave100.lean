/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixSheetSwapProjectorWave99
import InfoGeometry.Krein.DoubledSpaceMatrixProjectorTransportWave97
import InfoGeometry.Krein.DoubledSpaceMatrixProjectorMinusTransportWave98

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- The native doubled-space sheet swap exchanges the two Krein spectral
projectors.  This is the operator-level form of the matrix Peirce exchange. -/
theorem modular_j_conjugates_krein_projector_plus :
    (modular_j (E := E)).comp
      ((KreinSpace.P_plus (H := DoubledSpace E)).comp
        (modular_j (E := E))) =
      KreinSpace.P_minus (H := DoubledSpace E) := by
  calc
    (modular_j (E := E)).comp
        ((KreinSpace.P_plus (H := DoubledSpace E)).comp
          (modular_j (E := E))) =
        (ρclock (E := E) matrixJ).comp
          (((ρclock (E := E)) ((1 / 2 : ℝ) •
            ((1 : Matrix (Fin 2) (Fin 2) ℝ) + matrixEpsilon))).comp
            (ρclock (E := E) matrixJ)) := by
              rw [ρclock_matrixJ, ρclock_matrixEpsilon_projector_plus]
    _ = ρclock (E := E) ((1 / 2 : ℝ) •
          ((1 : Matrix (Fin 2) (Fin 2) ℝ) - matrixEpsilon)) :=
      ρclock_matrixJ_conjugates_matrixEpsilon_projector_plus (E := E)
    _ = KreinSpace.P_minus (H := DoubledSpace E) :=
      ρclock_matrixEpsilon_projector_minus (E := E)

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.modular_j_conjugates_krein_projector_plus
