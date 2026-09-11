import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows
import InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe

/-!
# Quotient-level witness transport

The CAS factorization need not be an equality of the current Lean group
representative.  This owner records the weaker, correct quotient statement.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness

open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows
open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev CarrierQuotient :=
  SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup

theorem quotientRepresentative_eq_left_smul_of_pc_matrix
    (i : Fin 189) (b w : SplitOctF2Aut)
    (h : ∃ e : PCWordExp,
      autMatrix ((flagRepresentative i)⁻¹ * (b * w)) =
        autMatrix (pcWord e)) :
    quotientRepresentative i =
      b • (QuotientGroup.mk w : CarrierQuotient) := by
  change QuotientGroup.mk (flagRepresentative i) =
    QuotientGroup.mk (b * w)
  rw [QuotientGroup.eq]
  obtain ⟨e, he⟩ := h
  have hgroup :
      (flagRepresentative i)⁻¹ * (b * w) = pcWord e :=
    autMatrix_injective he
  rw [hgroup]
  exact ⟨e, rfl⟩

theorem quotient_orbit_witness_of_collected_factorization
    (k : Fin 12) (i : Fin 189)
    (hfac : flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (rightFactorWord k i)) :
    ∃ b : SplitOctF2Aut,
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
        quotientRepresentative i =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) : CarrierQuotient) := by
  let b : SplitOctF2Aut := collect (leftFactorWord k i)
  let w : SplitOctF2Aut := weylNF (orbitWeyl k).1 (orbitWeyl k).2
  refine ⟨b, collect_mem_unipotentSubgroup _, ?_⟩
  change quotientRepresentative i =
    b • (QuotientGroup.mk w : CarrierQuotient)
  change QuotientGroup.mk (flagRepresentative i) =
    QuotientGroup.mk (b * w)
  rw [QuotientGroup.eq]
  have hri :
      (collect (rightFactorWord k i))⁻¹ ∈
        G2TwoPCSubgroupClosure.unipotentSubgroup :=
    G2TwoPCSubgroupClosure.unipotentSubgroup.inv_mem
      (collect_mem_unipotentSubgroup _)
  obtain ⟨e, he⟩ := hri
  refine ⟨e, ?_⟩
  rw [hfac]
  simp [b, w, mul_assoc]
  rw [← he]

theorem quotient_witness_cell_one_45 :
    quotientRepresentative 45 =
    collect (leftFactorWord 1 45) •
        (QuotientGroup.mk
          (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  rw [quotientRepresentative,
    InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe.cell_one_45_factorization]
  change QuotientGroup.mk
      (collect (leftFactorWord 1 45) *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
          collect (rightFactorWord 1 45)) =
    QuotientGroup.mk (collect (leftFactorWord 1 45) *
      weylNF (orbitWeyl 1).1 (orbitWeyl 1).2)
  rw [QuotientGroup.eq]
  have hri :
      (collect (rightFactorWord 1 45))⁻¹ ∈
        G2TwoPCSubgroupClosure.unipotentSubgroup :=
    G2TwoPCSubgroupClosure.unipotentSubgroup.inv_mem
      (collect_mem_unipotentSubgroup _)
  obtain ⟨e, he⟩ := hri
  refine ⟨e, ?_⟩
  simp [mul_assoc]
  rw [← he]

theorem quotient_witness_cell_four_18 :
    quotientRepresentative 18 =
      collect (rightFactorWord 4 18) •
        (QuotientGroup.mk
          (weylNF (orbitWeyl 4).1 (orbitWeyl 4).2) : CarrierQuotient) := by
  change QuotientGroup.mk (flagRepresentative 18) =
    QuotientGroup.mk
      (collect (rightFactorWord 4 18) *
        weylNF (orbitWeyl 4).1 (orbitWeyl 4).2)
  rw [QuotientGroup.eq]
  rw [row_4_18]
  simp only [mul_assoc, mul_inv_rev]
  have hri :
      (collect (leftFactorWord 4 18))⁻¹ ∈
        G2TwoPCSubgroupClosure.unipotentSubgroup :=
    G2TwoPCSubgroupClosure.unipotentSubgroup.inv_mem
      (collect_mem_unipotentSubgroup _)
  obtain ⟨e, he⟩ := hri
  refine ⟨e, ?_⟩
  simp
  rw [← he]

set_option maxRecDepth 100000 in
theorem quotient_witness_cell_one_73 :
    quotientRepresentative 73 =
    collect (leftFactorWord 1 73) •
        (QuotientGroup.mk
          (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  apply quotientRepresentative_eq_left_smul_of_pc_matrix
  exact InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe.cell_one_73_left_quotient_matrix

set_option maxRecDepth 100000 in
theorem quotient_witness_cell_one_178 :
    quotientRepresentative 178 =
    collect (leftFactorWord 1 178) •
        (QuotientGroup.mk
          (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  apply quotientRepresentative_eq_left_smul_of_pc_matrix
  exact InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe.cell_one_178_left_quotient_matrix

theorem hcell_one (i : Fin 189) (hi : i ∈ orbitCells 1) :
    ∃ b : SplitOctF2Aut,
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  have hi' : i = 24 ∨ i = 45 ∨ i = 178 ∨ i = 73 := by
    simpa [orbitCells, flagCells] using hi
  rcases hi' with rfl | rfl | rfl | rfl
  · exact ⟨1, G2TwoPCSubgroupClosure.unipotentSubgroup.one_mem,
      orbitCellAnchor_quotient_eq 1⟩
  · exact ⟨collect (leftFactorWord 1 45),
      collect_mem_unipotentSubgroup _, quotient_witness_cell_one_45⟩
  · exact ⟨collect (leftFactorWord 1 178),
      collect_mem_unipotentSubgroup _, quotient_witness_cell_one_178⟩
  · exact ⟨collect (leftFactorWord 1 73),
      collect_mem_unipotentSubgroup _, quotient_witness_cell_one_73⟩

theorem hcell_anchor (k : Fin 12) :
    ∃ b : SplitOctF2Aut,
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
        orbitEnum (orbitCellAnchor k) = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) : CarrierQuotient) := by
  exact ⟨1, G2TwoPCSubgroupClosure.unipotentSubgroup.one_mem,
    orbitCellAnchor_quotient_eq k⟩

end InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
