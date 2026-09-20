import InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
import InfoGeometry.Canonical.SouriauOnsagerBKMStrictPositivity
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The scalar gauge quotient of finite BKM observables

This module reuses the existing faithful density, centering operation, and BKM
integral. Centering is a real linear projection whose kernel is exactly the
real scalar multiples of the identity. The existing centered covariance
therefore induces a symmetric positive definite bilinear form on the native
submodule quotient. No new density carrier or modular conjugation is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.BKMScalarGaugeQuotient

open SouriauOnsagerBKM
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance

variable {n : ℕ}

def scalarGauge (n : ℕ) : Submodule ℝ (Operator n) :=
  Submodule.span ℝ {(1 : Operator n)}

def centeringLinearMap (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) : Operator n →ₗ[ℝ] Operator n :=
  LinearMap.id - (density.bkmRealBilinForm continuous_powers 1).smulRight 1

@[simp] theorem centeringLinearMap_apply (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) (observable : Operator n) :
    centeringLinearMap density continuous_powers observable =
      centeredStatistic density observable := by
  change observable - density.bkmRealBilinForm continuous_powers 1 observable • 1 = _
  rw [bkmRealBilinForm_one_left]
  rfl

@[simp] theorem centeringLinearMap_one (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) :
    centeringLinearMap density continuous_powers 1 = 0 := by
  change (1 : Operator n) - density.bkmRealBilinForm continuous_powers 1 1 • 1 = 0
  rw [bkmRealBilinForm_one_one]
  rw [zero_smul, sub_self]

theorem centeringLinearMap_idempotent (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) (observable : Operator n) :
    centeringLinearMap density continuous_powers
      (centeringLinearMap density continuous_powers observable) =
        centeringLinearMap density continuous_powers observable := by
  simp only [centeringLinearMap_apply]
  change centeredStatistic density observable -
    expectationReal density (centeredStatistic density observable) • (1 : Operator n) = _
  rw [expectationReal_centeredStatistic density continuous_powers]
  simp

theorem centeredStatistic_add_scalar (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) (observable : Operator n) (scalar : ℝ) :
    centeredStatistic density (observable + scalar • (1 : Operator n)) =
      centeredStatistic density observable := by
  rw [← centeringLinearMap_apply density continuous_powers,
    map_add, map_smul, centeringLinearMap_one]
  simp

theorem centeringLinearMap_ker (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) :
    LinearMap.ker (centeringLinearMap density continuous_powers) = scalarGauge n := by
  ext observable
  constructor
  · intro centered_zero
    have scalar_eq : observable = expectationReal density observable • (1 : Operator n) := by
      have centered_zero' : centeringLinearMap density continuous_powers observable = 0 :=
        centered_zero
      rw [centeringLinearMap_apply] at centered_zero'
      exact sub_eq_zero.mp centered_zero'
    rw [scalar_eq]
    exact Submodule.smul_mem (scalarGauge n) _
      (Submodule.subset_span (Set.mem_singleton (1 : Operator n)))
  · intro scalar_member
    obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp scalar_member
    change centeringLinearMap density continuous_powers (scalar • (1 : Operator n)) = 0
    rw [map_smul, centeringLinearMap_one, smul_zero]

theorem centeredStatistic_eq_zero_iff (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) (observable : Operator n) :
    centeredStatistic density observable = 0 ↔ observable ∈ scalarGauge n := by
  rw [← centeringLinearMap_apply density continuous_powers]
  change observable ∈ LinearMap.ker (centeringLinearMap density continuous_powers) ↔ _
  rw [centeringLinearMap_ker]

theorem centeredBKMRealCovariance_eq_zero_iff (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) (observable : Operator n) :
    centeredBKMRealCovariance density continuous_powers observable observable = 0 ↔
      observable ∈ scalarGauge n := by
  rw [centeredBKMRealCovariance_self, FaithfulDensityOperator.bkmRealBilinForm_apply,
    density.kuboMoriPairing_self_re_eq_zero_iff _ continuous_powers,
    centeredStatistic_eq_zero_iff density continuous_powers]

theorem centeredBKMRealCovariance_add_scalars (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) (left right : Operator n)
    (left_scalar right_scalar : ℝ) :
    centeredBKMRealCovariance density continuous_powers
      (left + left_scalar • (1 : Operator n))
      (right + right_scalar • (1 : Operator n)) =
        centeredBKMRealCovariance density continuous_powers left right := by
  unfold centeredBKMRealCovariance
  rw [centeredStatistic_add_scalar density continuous_powers,
    centeredStatistic_add_scalar density continuous_powers]

def centeredRepresentative (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) :
    (Operator n ⧸ scalarGauge n) →ₗ[ℝ] Operator n :=
  Submodule.liftQSpanSingleton (1 : Operator n)
    (centeringLinearMap density continuous_powers)
    (centeringLinearMap_one density continuous_powers)

@[simp] theorem centeredRepresentative_mk (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) (observable : Operator n) :
    centeredRepresentative density continuous_powers (Submodule.Quotient.mk observable) =
      centeredStatistic density observable :=
  centeringLinearMap_apply density continuous_powers observable

def quotientBKMForm (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) :
    LinearMap.BilinForm ℝ (Operator n ⧸ scalarGauge n) :=
  (density.bkmRealBilinForm continuous_powers).compl₁₂
    (centeredRepresentative density continuous_powers)
    (centeredRepresentative density continuous_powers)

@[simp] theorem quotientBKMForm_mk (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow) (left right : Operator n) :
    quotientBKMForm density continuous_powers
      (Submodule.Quotient.mk left) (Submodule.Quotient.mk right) =
        centeredBKMRealCovariance density continuous_powers left right := by
  unfold quotientBKMForm
  rw [LinearMap.compl₁₂_apply, centeredRepresentative_mk, centeredRepresentative_mk]
  rfl

theorem quotientBKMForm_symm (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow)
    (left right : Operator n ⧸ scalarGauge n) :
    quotientBKMForm density continuous_powers left right =
      quotientBKMForm density continuous_powers right left :=
  (density.bkmRealBilinForm_symm continuous_powers).eq _ _

theorem quotientBKMForm_pos (density : FaithfulDensityOperator n)
    (continuous_powers : Continuous density.rpow)
    (direction : Operator n ⧸ scalarGauge n) (nonzero : direction ≠ 0) :
    0 < quotientBKMForm density continuous_powers direction direction := by
  obtain ⟨observable, rfl⟩ := (scalarGauge n).mkQ_surjective direction
  change 0 < quotientBKMForm density continuous_powers
    (Submodule.Quotient.mk observable) (Submodule.Quotient.mk observable)
  rw [quotientBKMForm_mk, centeredBKMRealCovariance_self,
    FaithfulDensityOperator.bkmRealBilinForm_apply]
  apply density.kuboMoriPairing_self_pos _ continuous_powers
  intro centered_zero
  apply nonzero
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((centeredStatistic_eq_zero_iff density continuous_powers observable).mp centered_zero)

end InfoGeometry.Canonical.BKMScalarGaugeQuotient
