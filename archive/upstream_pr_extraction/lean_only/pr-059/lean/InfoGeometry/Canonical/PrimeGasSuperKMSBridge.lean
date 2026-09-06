import InfoGeometry.Canonical.AlgebraicKMSStateColimit

/-!
# Noncommutative primon KMS carrier

The former version of this file packaged unrelated real-valued readouts and
called their stored equalities a super-KMS bridge.  The native owner is the
algebraic Cuntz matrix colimit: a KMS datum is an invertible colimit density,
and its boundary identity is proved by noncommutative multiplication and
trace cyclicity.

No scalar temperature packet or equality-only surrogate is introduced here.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.PrimeGasSuperKMS

open InfoGeometry.Canonical.AlgebraicKMSStateColimit

/-- A primon KMS bridge is an actual invertible density in the noncommutative
algebraic Cuntz matrix colimit. -/
structure PrimeGasSuperKMSBridge where
  density : Carrierˣ

namespace PrimeGasSuperKMSBridge

variable (B : PrimeGasSuperKMSBridge)

/-- The native imaginary-time automorphism determined by the bridge density. -/
def imaginaryTime : Carrier ≃ₐ[ℂ] Carrier :=
  deltaImaginaryTimeAlgEquiv B.density

/-- The actual noncommutative KMS boundary identity carried by the bridge. -/
theorem kms_boundary (x y : Carrier) :
    deltaWeightedFunctional B.density (x * y) =
      deltaWeightedFunctional B.density (y * B.imaginaryTime x) := by
  exact deltaWeightedFunctional_kms B.density x y

end PrimeGasSuperKMSBridge

end InfoGeometry.Canonical.PrimeGasSuperKMS

end noncomputable section
