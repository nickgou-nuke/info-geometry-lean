/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect

/-!
# Dependence of Peirce generators on off-diagonal data

Adding even Peirce components to the inputs of the two cones does not change
the cones. Consequently the tetraktys and the transfer defect depend only on
the off-diagonal input components. This is an algebraic block statement; it
does not assert a physical area law.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P)
include hP

theorem conePlus_evenGrade_zero (X : B) :
    conePlus P (evenGrade P X) = 0 := by
  simp only [conePlus, evenGrade, mul_add, add_mul]
  peirce_nf hP

theorem coneMinus_evenGrade_zero (X : B) :
    coneMinus P (evenGrade P X) = 0 := by
  simp only [coneMinus, evenGrade, mul_add, add_mul]
  peirce_nf hP

theorem conePlus_evenGrade_shift (A X : B) :
    conePlus P (A + evenGrade P X) = conePlus P A := by
  rw [conePlus_add P A (evenGrade P X), conePlus_evenGrade_zero hP]
  simp

theorem coneMinus_evenGrade_shift (C X : B) :
    coneMinus P (C + evenGrade P X) = coneMinus P C := by
  rw [coneMinus_add P C (evenGrade P X), coneMinus_evenGrade_zero hP]
  simp

theorem tetraktys_evenGrade_shift (A C X Y : B) :
    genPhi P (A + evenGrade P X) (C + evenGrade P Y) = genPhi P A C ∧
    genJ P (A + evenGrade P X) (C + evenGrade P Y) = genJ P A C ∧
    genV P (A + evenGrade P X) (C + evenGrade P Y) = genV P A C ∧
    genSig P (A + evenGrade P X) (C + evenGrade P Y) = genSig P A C := by
  have hPlus := conePlus_evenGrade_shift hP A X
  have hMinus := coneMinus_evenGrade_shift hP C Y
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [genPhi, hPlus, hMinus]
  · simp only [genJ, hPlus, hMinus]
  · simp only [genV, hPlus, hMinus]
  · simp only [genSig, hPlus, hMinus]

theorem peirceTransfer_defect_evenGrade_shift (A C X Y : B) :
    idempotencyDefect
        (peirceTransfer P (A + evenGrade P X) (C + evenGrade P Y)) =
      idempotencyDefect (peirceTransfer P A C) := by
  rw [(peirceTransfer_defect_and_vieta hP
    (A + evenGrade P X) (C + evenGrade P Y)).1,
    (peirceTransfer_defect_and_vieta hP A C).1,
    (tetraktys_evenGrade_shift hP A C X Y).2.2.1]

end InfoGeometry.OperatorAlgebra.PeirceSpine
