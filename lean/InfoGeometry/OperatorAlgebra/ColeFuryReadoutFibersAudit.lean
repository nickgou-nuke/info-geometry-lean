/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ColeFuryReadoutFibers
import InfoGeometry.OperatorAlgebra.ColeFuryIdeals

namespace InfoGeometry.OperatorAlgebra.ColeFury

example : kernelElement = invisibleContrasts 1 (-1) 0 0 := by decide

example : quadrantReadout (invisibleContrasts 2 3 4 5) = 0 :=
  quadrantReadout_contrasts 2 3 4 5

theorem readout_horizons_noncommuting : horizonUp * horizonDown ≠ horizonDown * horizonUp := by
  rw [horizonUp_horizonDown, horizonDown_horizonUp]
  intro h
  have he := congrArg (fun M : Spin32Matrix => M 0 0) h
  norm_num [upperLeft, lowerRight] at he

#print axioms quadrantReadout_eq_iff
#print axioms quadrantReadout_representative
#print axioms quadrantReadout_contrasts
#print axioms aggregate_reconstruction
#print axioms quadrantReadout_kernel_iff
#print axioms embed_not_injective
#print axioms readout_horizons_noncommuting

end InfoGeometry.OperatorAlgebra.ColeFury
