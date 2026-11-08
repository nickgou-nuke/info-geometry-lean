import InfoGeometry.Canonical.GibbsHessianScalarGaugeBridge

noncomputable section

namespace InfoGeometry.Canonical.BKMScalarGaugeQuotientTests

open SouriauOnsagerBKM
open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.GibbsHessianScalarGaugeBridge

variable {n : ℕ} (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow)

example (observable : FiniteOperatorAlgebra n) :
    centeringLinearMap density continuous_powers
      (centeringLinearMap density continuous_powers observable) =
        centeringLinearMap density continuous_powers observable :=
  centeringLinearMap_idempotent density continuous_powers observable

example (left right : FiniteOperatorAlgebra n) (left_scalar right_scalar : ℝ) :
    centeredBKMRealCovariance density continuous_powers
      (left + left_scalar • (1 : FiniteOperatorAlgebra n))
      (right + right_scalar • (1 : FiniteOperatorAlgebra n)) =
        centeredBKMRealCovariance density continuous_powers left right :=
  centeredBKMRealCovariance_add_scalars density continuous_powers
    left right left_scalar right_scalar

example (observable : FiniteOperatorAlgebra n) :
    centeredBKMRealCovariance density continuous_powers observable observable = 0 ↔
      ∃ scalar : ℝ, scalar • (1 : FiniteOperatorAlgebra n) = observable := by
  rw [centeredBKMRealCovariance_eq_zero_iff]
  exact Submodule.mem_span_singleton

example (direction : FiniteOperatorAlgebra n ⧸ scalarGauge n) (nonzero : direction ≠ 0) :
    0 < quotientBKMForm density continuous_powers direction direction :=
  quotientBKMForm_pos density continuous_powers direction nonzero

#print axioms centeringLinearMap_ker
#print axioms centeredBKMRealCovariance_eq_zero_iff
#print axioms quotientBKMForm_pos
#print axioms secondFDeriv_logPartition_eq_quotientBKMForm
#print axioms secondFDeriv_logPartition_self_eq_zero_iff
#print axioms parameter_hessian_self_pos

end InfoGeometry.Canonical.BKMScalarGaugeQuotientTests
