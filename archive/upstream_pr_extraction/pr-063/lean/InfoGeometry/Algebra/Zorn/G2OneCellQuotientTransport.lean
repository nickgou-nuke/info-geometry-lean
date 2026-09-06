import InfoGeometry.Algebra.Zorn.G2CASFactorizationProbe
import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

namespace InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2BNPair
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem cell_one_left_quotient_matrix
    (i : Fin 189) (hi : i ∈ orbitCells 1) :
    ∃ e : PCWordExp,
      autMatrix ((flagRepresentative i)⁻¹ *
        (collect (leftFactorWord 1 i) *
          weylNF (orbitWeyl 1).1 (orbitWeyl 1).2)) =
        autMatrix (pcWord e) := by
  fin_cases i <;> simp_all [orbitCells, flagCells]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem cell_one_quotient_witness
    (i : Fin 189) (hi : i ∈ orbitCells 1) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        quotientRepresentative i =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) :
              G2FlagCellQuotientWitness.CarrierQuotient) := by
  obtain ⟨e, he⟩ := cell_one_left_quotient_matrix i hi
  let b := collect (leftFactorWord 1 i)
  refine ⟨b, collect_mem_unipotentSubgroup _, ?_⟩
  exact quotientRepresentative_eq_left_smul_of_pc_matrix i b
    (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) ⟨e, he⟩

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem all_cells_left_quotient_matrix
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    ∃ e : PCWordExp,
      autMatrix ((flagRepresentative i)⁻¹ *
        (collect (leftFactorWord k i) *
          weylNF (orbitWeyl k).1 (orbitWeyl k).2)) =
        autMatrix (pcWord e) := by
  fin_cases k <;> fin_cases i <;> simp_all [orbitCells, flagCells]

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem all_cells_quotient_witness
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        quotientRepresentative i =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
              G2FlagCellQuotientWitness.CarrierQuotient) := by
  obtain ⟨e, he⟩ := all_cells_left_quotient_matrix k i hi
  let b := collect (leftFactorWord k i)
  refine ⟨b, collect_mem_unipotentSubgroup _, ?_⟩
  exact quotientRepresentative_eq_left_smul_of_pc_matrix i b
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2) ⟨e, he⟩

theorem all_cells_orbitEnum_hcell
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
              G2FlagCellQuotientWitness.CarrierQuotient) := by
  exact all_cells_quotient_witness k i hi

theorem all_cells_representative_mem
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i ∈
      concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2) := by
  rw [concreteBruhatCell_eq_exact_unipotentCell]
  apply (mem_doubleCoset_iff_quotient_smul
    unipotentSubgroup
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2)
    (flagRepresentative i)).2
  obtain ⟨b, hb, hq⟩ := all_cells_quotient_witness k i hi
  exact ⟨b, hb, hq.symm⟩

end InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport
