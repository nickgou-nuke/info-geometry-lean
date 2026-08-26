import InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate
import InfoGeometry.Algebra.Zorn.G2ReducedWords

/-!
# Quotient-to-residual transport from a concrete Bruhat certificate

This owner records the exact reusable bridge supplied by a genuine concrete
certificate.  It does not construct the certificate or assert global quotient
exhaustion on its own.
-/

namespace InfoGeometry.Algebra.Zorn.G2QuotientCanonicalResidualEquiv

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2ReducedWords

noncomputable def quotientEquivCanonicalResidual
  (enum : Fin 189 ≃ CarrierQuotient) :
    CarrierQuotient ≃
      (Σ w : G2WeylElement, Fin (weylLength w) → Bool) :=
  enum.symm.trans canonicalBinaryFlagIndexEquiv.symm

end InfoGeometry.Algebra.Zorn.G2QuotientCanonicalResidualEquiv
