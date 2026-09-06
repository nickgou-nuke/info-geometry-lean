import InfoGeometry.Canonical.NoncommutativeGibbsNormalizedBKMTwoPointBridge
import InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance

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

end InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge
