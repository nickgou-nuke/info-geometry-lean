import InfoGeometry.Canonical.BKMScalarGaugeQuotient
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge

/-!
# The Gibbs Hessian on scalar-gauge classes

The genuine noncommutative Gibbs Hessian and its parameter pullback remain
owned by `NoncommutativeGibbsBKMHessianBridge`. This bridge identifies their
scalar null directions using the positive BKM form on the quotient by `ℝ • 1`.
It does not assert a global geodesic distance or an infinite-dimensional chart.
-/

noncomputable section

namespace InfoGeometry.Canonical.GibbsHessianScalarGaugeBridge

open SouriauOnsagerBKM
open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge

variable {n : ℕ}

theorem secondFDeriv_logPartition_eq_quotientBKMForm
    (exponent left right : FiniteOperatorAlgebra n)
    (self_adjoint : IsSelfAdjoint exponent)
    (positive_partition : 0 < gibbsPartitionReal exponent)
    (left_self_adjoint : IsSelfAdjoint left) :
    (secondFDerivLogPartitionReadout exponent left right).re =
      quotientBKMForm (faithfulGibbsDensity exponent self_adjoint positive_partition)
        (continuous_faithfulGibbsDensity_rpow exponent self_adjoint positive_partition)
        (Submodule.Quotient.mk left) (Submodule.Quotient.mk right) := by
  rw [quotientBKMForm_mk]
  exact secondFDeriv_logPartition_apply_eq_centeredBKM
    exponent self_adjoint positive_partition left right left_self_adjoint

theorem secondFDeriv_logPartition_self_eq_zero_iff
    (exponent direction : FiniteOperatorAlgebra n)
    (self_adjoint : IsSelfAdjoint exponent)
    (positive_partition : 0 < gibbsPartitionReal exponent)
    (direction_self_adjoint : IsSelfAdjoint direction) :
    (secondFDerivLogPartitionReadout exponent direction direction).re = 0 ↔
      direction ∈ scalarGauge n := by
  rw [secondFDeriv_logPartition_apply_eq_centeredBKM
    exponent self_adjoint positive_partition direction direction direction_self_adjoint]
  exact centeredBKMRealCovariance_eq_zero_iff _ _ direction

theorem parameter_hessian_self_eq_zero_iff
    {Parameters : Type*} [AddCommGroup Parameters] [Module ℝ Parameters]
    (density : FaithfulDensityOperator n) (continuous_powers : Continuous density.rpow)
    (statistics : Parameters →ₗ[ℝ] FiniteOperatorAlgebra n) (direction : Parameters) :
    centeredBKMOperatorBilinForm density continuous_powers
      statistics statistics direction direction = 0 ↔
        statistics direction ∈ scalarGauge n :=
  centeredBKMRealCovariance_eq_zero_iff density continuous_powers (statistics direction)

theorem parameter_hessian_self_pos
    {Parameters : Type*} [AddCommGroup Parameters] [Module ℝ Parameters]
    (density : FaithfulDensityOperator n) (continuous_powers : Continuous density.rpow)
    (statistics : Parameters →ₗ[ℝ] FiniteOperatorAlgebra n) (direction : Parameters)
    (identifiable : statistics direction ∉ scalarGauge n) :
    0 < centeredBKMOperatorBilinForm density continuous_powers
      statistics statistics direction direction := by
  change 0 < centeredBKMRealCovariance density continuous_powers
    (statistics direction) (statistics direction)
  rw [← quotientBKMForm_mk]
  apply quotientBKMForm_pos
  intro zero_class
  exact identifiable (Submodule.Quotient.mk_eq_zero.mp zero_class)

end InfoGeometry.Canonical.GibbsHessianScalarGaugeBridge
