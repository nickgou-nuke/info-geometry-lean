import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Base point of the native flag representative map

The first certificate word is the empty word.  This small owner records its
concrete quotient interpretation without asserting the still-open global
quotient enumeration theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagRepresentativeBase

open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordEvaluator
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem flagRepresentative_zero_eq_one :
    flagRepresentative 0 = (1 : SplitOctF2Aut) := by
  rfl

theorem quotientRepresentative_zero_eq_identity :
    quotientRepresentative 0 =
      (QuotientGroup.mk 1 : CarrierQuotient) := by
  rw [quotientRepresentative, flagRepresentative_zero_eq_one]

theorem quotientRepresentative_zero_eq_identity_iff
    (i : Fin 189) :
    quotientRepresentative i = quotientRepresentative 0 ↔
      (flagRepresentative i)⁻¹ ∈
        G2TwoPCSubgroupClosure.unipotentSubgroup := by
  rw [quotientRepresentative_eq_iff, flagRepresentative_zero_eq_one]
  change (flagRepresentative i)⁻¹ ∈
      G2TwoPCSubgroupClosure.unipotentSubgroup ↔
    (flagRepresentative i)⁻¹ ∈
      G2TwoPCSubgroupClosure.unipotentSubgroup
  rfl

end InfoGeometry.Algebra.Zorn.G2FlagRepresentativeBase
