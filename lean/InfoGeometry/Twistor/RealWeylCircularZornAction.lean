/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
import InfoGeometry.Twistor.PenroseCanonicalZornSoldering

/-!
# The paired Weyl action on the circular Zorn carrier

The identification is real-linear and transports the full spin-group action.
No compatibility with the Zorn product or its quadratic form is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealWeylCircularZornAction

open InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Twistor.PenroseCanonicalZornSoldering

/-- The first and last two complex coordinates form the two Weyl sheets. -/
def twistorWeylEquiv : TwistorCarrier ≃ₗ[ℝ] WeylPair where
  toFun z := ( ![z 0, z 1], ![z 2, z 3] )
  invFun p := ![p.1 0, p.1 1, p.2 0, p.2 1]
  left_inv z := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_add' z w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' r z := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- Read the two Weyl spinors from the circular Zorn carrier. -/
def zornWeylEquiv : CanonicalZorn ≃ₗ[ℝ] WeylPair :=
  penroseCanonicalZornEquiv.symm.trans twistorWeylEquiv

/-- Transport of the paired spin action, with its two distinct chiral factors. -/
def zornWeylAction (g : SL2C) (z : CanonicalZorn) : CanonicalZorn :=
  zornWeylEquiv.symm (actWeylPair g (zornWeylEquiv z))

theorem zornWeylAction_readout (g : SL2C) (z : CanonicalZorn) :
    zornWeylEquiv (zornWeylAction g z) = actWeylPair g (zornWeylEquiv z) := by
  simp [zornWeylAction]

theorem zornWeylAction_one (z : CanonicalZorn) : zornWeylAction 1 z = z := by
  simp [zornWeylAction]

theorem zornWeylAction_mul (g h : SL2C) (z : CanonicalZorn) :
    zornWeylAction (g * h) z = zornWeylAction g (zornWeylAction h z) := by
  apply zornWeylEquiv.injective
  simp only [zornWeylAction_readout, actWeylPair_mul]

theorem zornWeylAction_left (g : SL2C) (z : CanonicalZorn) :
    (zornWeylEquiv (zornWeylAction g z)).1 =
      matrixSpinAction (g : Mat2C) (zornWeylEquiv z).1 := by
  rw [zornWeylAction_readout]
  rfl

theorem zornWeylAction_right (g : SL2C) (z : CanonicalZorn) :
    (zornWeylEquiv (zornWeylAction g z)).2 =
      matrixSpinAction (rightWeyl g : Mat2C) (zornWeylEquiv z).2 := by
  rw [zornWeylAction_readout]
  rfl

end InfoGeometry.Twistor.RealWeylCircularZornAction
