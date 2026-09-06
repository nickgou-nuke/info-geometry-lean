import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.L2Multiplier

open scoped ENNReal
open MeasureTheory

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace L2Multiplier

section Audit

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

example :
    ENNReal.HolderTriple
      (∞ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := by
  infer_instance

#check L2c
#check Linftyc
#check mulOp
#check mulOp_apply
#check mulOp_apply_ae
#check norm_mulOp_apply_le
#check norm_mulOp_le
#check mulOpBilinear

#check ell2Count
#check ellInfCount
#check discreteMulOp
#check discreteMulOp_apply
#check discreteMulOp_apply_pointwise
#check norm_discreteMulOp_apply_le
#check norm_discreteMulOp_le

#check MeasureTheory.Lp.coeFn_lpSMul
#check MeasureTheory.Lp.norm_smul_le
#check MeasureTheory.Measure.ae_count_iff
#check ContinuousLinearMap.holderL
#check ContinuousLinearMap.mul

end Audit

end L2Multiplier
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

