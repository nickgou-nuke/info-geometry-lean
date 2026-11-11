/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.OrderedHomotope
import InfoGeometry.Twistor.PerjesMomentOperator

/-! # A noncommuting homotope with a square-zero twistor kernel

The witness lives in the existing mixed-index matrix algebra. Both the
kernel and one input are actual moment operators of null twistors.
-/

noncomputable section

namespace InfoGeometry.Twistor.MomentHomotopeWitness

open PerjesMomentOperator TwistorKinematicTensor
open InfoGeometry.OperatorAlgebra.OrderedHomotope

theorem square_zero_kernel_noncommuting :
    ∃ T X : KinematicMatrix,
      T * T = 0 ∧ X * X = 0 ∧ bracket T X 1 ≠ 0 := by
  obtain ⟨Z, W, hZ, hW, hcomm⟩ := momentOperators_noncommuting
  refine ⟨momentOperator W, momentOperator Z,
    null_momentOperator_square W hW, null_momentOperator_square Z hZ, ?_⟩
  rw [bracket_ne_zero_iff]
  simpa only [product, mul_one, one_mul] using hcomm

end InfoGeometry.Twistor.MomentHomotopeWitness
