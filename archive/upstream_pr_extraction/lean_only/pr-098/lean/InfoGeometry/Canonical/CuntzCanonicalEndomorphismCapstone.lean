import InfoGeometry.Canonical.CuntzCanonicalEndomorphismBridge

namespace InfoGeometry.Canonical.CuntzCanonicalEndomorphismCapstone

open InfoGeometry.Canonical.CuntzEndomorphism

/--
🏆 **CAPSTONE: Canonical Verification of the Cuntz Endomorphism & KMS Invariance**
-/
theorem cuntz_canonical_endomorphism_canonical_capstone
    {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzTwoAlgebra Op)
    (phiState : KMSStateFunctional Op)
    (X : Op) :
    (star C.sL * C.sL = 1 ∧ star C.sR * C.sR = 1) ∧
    (C.sL * star C.sL + C.sR * star C.sR = 1) ∧
    (cuntzMap C 1 = 1) ∧
    (phiState.phi (cuntzMap C X) = phiState.phi X) :=
  grand_cuntz_endomorphism_synthesis C phiState X

end InfoGeometry.Canonical.CuntzCanonicalEndomorphismCapstone
