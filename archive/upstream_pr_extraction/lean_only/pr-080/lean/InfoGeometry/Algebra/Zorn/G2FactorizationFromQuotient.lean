import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval

namespace InfoGeometry.Algebra.Zorn.G2FactorizationFromQuotient

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-! A quotient witness contains an actual right-hand residual factor.  This
    lemma is purely algebraic: it does not inspect the finite flag table or
    use a computational equality oracle. -/
theorem factorization_of_quotient_witness
    (i : Fin 189) (b w : SplitOctF2Aut)
    (hq : quotientRepresentative i =
      b • (QuotientGroup.mk w :
        G2NativeQuotientRepresentative.CarrierQuotient)) :
    ∃ u : SplitOctF2Aut, u ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
      flagRepresentative i = b * w * u := by
  change QuotientGroup.mk (flagRepresentative i) =
    QuotientGroup.mk (b * w) at hq
  have hmem : (flagRepresentative i)⁻¹ * (b * w) ∈
      G2TwoPCSubgroupClosure.unipotentSubgroup := by
    exact (QuotientGroup.eq).mp hq
  refine ⟨((flagRepresentative i)⁻¹ * (b * w))⁻¹,
    G2TwoPCSubgroupClosure.unipotentSubgroup.inv_mem hmem, ?_⟩
  simp [mul_assoc]

theorem cell_one_factorization_exists
    (i : Fin 189) (hi : i ∈ orbitCells 1) :
    ∃ b u : SplitOctF2Aut,
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
      u ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
      flagRepresentative i =
        b * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * u := by
  obtain ⟨b, hb, hq⟩ := hcell_one i hi
  obtain ⟨u, hu, hfac⟩ := factorization_of_quotient_witness i b
    (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) hq
  exact ⟨b, u, hb, hu, hfac⟩

end InfoGeometry.Algebra.Zorn.G2FactorizationFromQuotient
