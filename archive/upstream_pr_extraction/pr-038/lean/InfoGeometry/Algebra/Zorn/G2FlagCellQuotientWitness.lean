import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

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
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev CarrierQuotient :=
  SplitOctF2Aut ⧸ G2TwoPCSubgroupClosure.unipotentSubgroup

def gapExp (support : List (Fin 6)) : PCWordExp :=
  fun i => decide (i ∈ support)

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

theorem quotient_witness_cell_one_45 :
    quotientRepresentative 45 =
    pcWord (gapExp [(1 : Fin 6), (4 : Fin 6)]) •
        (QuotientGroup.mk
          (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  apply quotientRepresentative_eq_left_smul_of_pc_matrix
  decide

set_option maxRecDepth 100000 in
theorem quotient_witness_cell_one_73 :
    quotientRepresentative 73 =
    pcWord (gapExp [(2 : Fin 6), (1 : Fin 6)]) •
        (QuotientGroup.mk
          (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  apply quotientRepresentative_eq_left_smul_of_pc_matrix
  decide

set_option maxRecDepth 100000 in
theorem quotient_witness_cell_one_178 :
    quotientRepresentative 178 =
    pcWord (gapExp [(4 : Fin 6), (2 : Fin 6)]) •
        (QuotientGroup.mk
          (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) : CarrierQuotient) := by
  apply quotientRepresentative_eq_left_smul_of_pc_matrix
  decide

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
  · exact ⟨pcWord (gapExp [(1 : Fin 6), (4 : Fin 6)]),
      ⟨gapExp [(1 : Fin 6), (4 : Fin 6)], rfl⟩,
      quotient_witness_cell_one_45⟩
  · exact ⟨pcWord (gapExp [(4 : Fin 6), (2 : Fin 6)]),
      ⟨gapExp [(4 : Fin 6), (2 : Fin 6)], rfl⟩,
      quotient_witness_cell_one_178⟩
  · exact ⟨pcWord (gapExp [(2 : Fin 6), (1 : Fin 6)]),
      ⟨gapExp [(2 : Fin 6), (1 : Fin 6)], rfl⟩,
      quotient_witness_cell_one_73⟩

theorem hcell_anchor (k : Fin 12) :
    ∃ b : SplitOctF2Aut,
      b ∈ G2TwoPCSubgroupClosure.unipotentSubgroup ∧
        orbitEnum (orbitCellAnchor k) = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) : CarrierQuotient) := by
  exact ⟨1, G2TwoPCSubgroupClosure.unipotentSubgroup.one_mem,
    orbitCellAnchor_quotient_eq k⟩

end InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
