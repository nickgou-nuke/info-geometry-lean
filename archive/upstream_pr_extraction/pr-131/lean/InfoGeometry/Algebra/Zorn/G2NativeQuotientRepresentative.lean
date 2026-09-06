import Mathlib.GroupTheory.GroupAction.Quotient
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/-!
# Native quotient representatives for the CAS-aligned 189-word table

This owner contains only facts that follow from the actual Lean carrier.  The
189 words define a map into the quotient by the concrete PC subgroup.  The
remaining injectivity and exhaustion statements are intentionally separate:
they require the corresponding carrier-aligned CAS certificate and are not
silently treated as consequences of the word table alone.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative

open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev CarrierQuotient :=
  SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup

noncomputable def quotientRepresentative (i : Fin 189) : CarrierQuotient :=
  QuotientGroup.mk (flagRepresentative i)

theorem quotientRepresentative_eq_iff (i j : Fin 189) :
    quotientRepresentative i = quotientRepresentative j ↔
      (flagRepresentative i)⁻¹ * flagRepresentative j ∈
        G2TwoPCSubgroupClosure.unipotentSubgroup := by
  change (QuotientGroup.mk (flagRepresentative i) : CarrierQuotient) =
      QuotientGroup.mk (flagRepresentative j) ↔ _
  rw [QuotientGroup.eq]

theorem quotientRepresentative_eq_of_right_factor
    (i j : Fin 189) (b : SplitOctF2Aut)
    (hb : b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup)
    (h : flagRepresentative j = flagRepresentative i * b) :
    quotientRepresentative i = quotientRepresentative j := by
  rw [quotientRepresentative_eq_iff, h]
  simpa [mul_assoc] using hb

theorem quotientRepresentative_eq_of_pc_matrix_factor
    (i j : Fin 189) (e : G2TwoSylowSubgroup.PCWordExp)
    (hmat : autMatrix ((flagRepresentative i)⁻¹ * flagRepresentative j) =
      autMatrix (G2TwoSylowSubgroup.pcWord e)) :
    quotientRepresentative i = quotientRepresentative j := by
  apply (quotientRepresentative_eq_iff i j).2
  have hgroup :
      (flagRepresentative i)⁻¹ * flagRepresentative j =
        G2TwoSylowSubgroup.pcWord e := by
    apply autMatrix_injective
    exact hmat
  rw [hgroup]
  exact ⟨e, rfl⟩

end InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
