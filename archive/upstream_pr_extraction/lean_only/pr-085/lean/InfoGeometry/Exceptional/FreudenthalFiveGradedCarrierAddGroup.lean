import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

noncomputable instance : AddCommGroup (FiveGradedCarrier D) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc u v w := by
    apply FiveGradedCarrier.ext <;>
      dsimp [FiveGradedCarrier.instAdd]
    all_goals exact add_assoc _ _ _
  zero_add u := by
    apply FiveGradedCarrier.ext <;>
      dsimp [FiveGradedCarrier.instAdd, FiveGradedCarrier.instZero]
    all_goals exact zero_add _
  add_zero u := by
    apply FiveGradedCarrier.ext <;>
      dsimp [FiveGradedCarrier.instAdd, FiveGradedCarrier.instZero]
    all_goals exact add_zero _
  neg_add_cancel u := by
    apply FiveGradedCarrier.ext <;>
      dsimp [FiveGradedCarrier.instAdd, FiveGradedCarrier.instNeg]
    all_goals exact neg_add_cancel _
  add_comm u v := by
    apply FiveGradedCarrier.ext <;>
      dsimp [FiveGradedCarrier.instAdd]
    all_goals exact add_comm _ _
  sub_eq_add_neg u v := by
    apply FiveGradedCarrier.ext <;>
      dsimp [FiveGradedCarrier.instSub, FiveGradedCarrier.instAdd,
        FiveGradedCarrier.instNeg]
    all_goals exact sub_eq_add_neg _ _

end InfoGeometry.Exceptional.Freudenthal
