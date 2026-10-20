/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpaceMatrixKreinAdjointWave94

noncomputable section

namespace InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- The matrix Peirce projector for `matrixEpsilon` is carried to the
native positive Krein projector. -/
theorem ρclock_matrixEpsilon_projector_plus :
    ρclock (E := E) ((1 / 2 : ℝ) •
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) + matrixEpsilon)) =
      KreinSpace.P_plus (H := DoubledSpace E) := by
  rw [map_smul, map_add, ρclock_one, ρclock_matrixEpsilon]
  have hε : KreinSpace.jCLM (H := DoubledSpace E) = spectral_epsilon (E := E) := by
    apply ContinuousLinearMap.ext
    intro u
    apply DoubledSpace.ext <;> rfl
  simp [KreinSpace.P_plus, KreinSpace.kreinSplitInvolution,
    InfoGeometry.GrandUnification.ArchetypeDictionary.SplitInvolution.P_plus,
    InfoGeometry.GrandUnification.ArchetypeDictionary.peircePlus, hε]
  ext u <;> simp only [ContinuousLinearMap.id_apply, one_apply_eq_self]

end InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

#print axioms InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock_matrixEpsilon_projector_plus
