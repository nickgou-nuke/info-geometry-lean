import InfoGeometry.Canonical.NoncommutativeGibbsNormalizedBKMTwoPointBridge
import InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity

/-!
# Centered Fréchet response and BKM covariance

This owner composes the normalized Fréchet--Kubo--Mori theorem with the
repository's centered BKM covariance algebra.  The result is deliberately
named a centered response: an actual Hessian theorem still requires packaging
the second derivative of the real log-partition map.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge

open SouriauOnsagerBKM
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsNormalizedBKMTwoPointBridge

abbrev Operator (n : ℕ) := FiniteOperatorAlgebra n

/-- Real centered response after subtracting the two first moments. -/
noncomputable def centeredFrechetResponse
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) : ℝ :=
  (normalizedFrechetTwoPoint H A B).re -
    expectationReal (faithfulGibbsDensity H hH hZ) A *
      expectationReal (faithfulGibbsDensity H hH hZ) B

/-- For self-adjoint A, the centered response is the native BKM covariance. -/
theorem centeredFrechetResponse_eq_centeredBKMRealCovariance
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) (hA : IsSelfAdjoint A) :
    centeredFrechetResponse H hH hZ A B =
      centeredBKMRealCovariance
        (faithfulGibbsDensity H hH hZ)
        (continuous_faithfulGibbsDensity_rpow H hH hZ)
        A B := by
  rw [centeredBKMRealCovariance_eq]
  rw [FaithfulDensityOperator.bkmRealBilinForm_apply]
  unfold centeredFrechetResponse
  rw [normalizedFrechetTwoPoint_eq_kuboMoriPairing H hH hZ A B]
  rw [hA.star_eq]

theorem centeredFrechetResponse_symm_of_selfAdjoint
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A B : Operator n) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    centeredFrechetResponse H hH hZ A B =
      centeredFrechetResponse H hH hZ B A := by
  rw [centeredFrechetResponse_eq_centeredBKMRealCovariance H hH hZ A B hA,
    centeredFrechetResponse_eq_centeredBKMRealCovariance H hH hZ B A hB]
  exact centeredBKMRealCovariance_symm
    (faithfulGibbsDensity H hH hZ)
    (continuous_faithfulGibbsDensity_rpow H hH hZ) A B

theorem centeredFrechetResponse_nonneg_selfAdjoint
    {n : ℕ} (H : Operator n) (hH : IsSelfAdjoint H)
    (hZ : 0 < gibbsPartitionReal H)
    (A : Operator n) (hA : IsSelfAdjoint A) :
    0 ≤ centeredFrechetResponse H hH hZ A A := by
  rw [centeredFrechetResponse_eq_centeredBKMRealCovariance H hH hZ A A hA]
  rw [centeredBKMRealCovariance_self]
  rw [FaithfulDensityOperator.bkmRealBilinForm_apply]
  exact FaithfulDensityOperator.kuboMoriPairing_self_re_nonneg
    (faithfulGibbsDensity H hH hZ)
    (centeredStatistic (faithfulGibbsDensity H hH hZ) A)
    (continuous_faithfulGibbsDensity_rpow H hH hZ)

end InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge
