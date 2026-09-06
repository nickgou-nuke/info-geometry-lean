import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

/-!
# Orientation-correct factorization transport

This owner isolates the algebraic step used by a concrete cell witness: a
right `U`-factor disappears in the quotient, while the left `U`-factor acts
by quotient smul.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge

open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem quotientRepresentative_eq_left_smul_of_factorization
    (i : Fin 189) (b₁ b₂ w : SplitOctF2Aut)
    (hb₂ : b₂ ∈ unipotentSubgroup)
    (hfac : flagRepresentative i = b₁ * w * b₂) :
    quotientRepresentative i =
      b₁ • (QuotientGroup.mk w : CarrierQuotient) := by
  change (QuotientGroup.mk (flagRepresentative i) : CarrierQuotient) =
    QuotientGroup.mk (b₁ * w)
  rw [hfac, QuotientGroup.eq]
  simpa [mul_assoc] using unipotentSubgroup.inv_mem hb₂

theorem flagRepresentative_mem_concreteBruhatCell_of_factorization
    (i : Fin 189) (b₁ b₂ w : SplitOctF2Aut)
    (hb₁ : b₁ ∈ unipotentSubgroup)
    (hb₂ : b₂ ∈ unipotentSubgroup)
    (hfac : flagRepresentative i = b₁ * w * b₂) :
    flagRepresentative i ∈ concreteBruhatCell w := by
  rw [concreteBruhatCell_eq_exact_unipotentCell]
  exact ⟨b₁, hb₁, b₂, hb₂, hfac⟩

end InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
