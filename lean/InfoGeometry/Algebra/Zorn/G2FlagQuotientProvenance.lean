import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
import InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows
import InfoGeometry.Algebra.Zorn.G2FactorizationFromQuotient

/-!
# Provenance-safe quotient row witnesses

These lemmas expose the already verified quotient witnesses without promoting
them to exact, uniformly oriented group factorizations.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagQuotientProvenance

open InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
open InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
open InfoGeometry.Algebra.Zorn.G2FlagFactorizationRows
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FactorizationFromQuotient

def QuotientRowWitness (k : Fin 12) (i : Fin 189) : Prop :=
  ∃ b : SplitOctF2Aut,
    b ∈ unipotentSubgroup ∧
      orbitEnum i = b •
        (QuotientGroup.mk
        (weylNF (orbitWeyl k).1 (orbitWeyl k).2) : CarrierQuotient)

theorem quotient_row_of_exact_factorization
    (k : Fin 12) (i : Fin 189)
    (b u : SplitOctF2Aut)
    (hb : b ∈ unipotentSubgroup)
    (hu : u ∈ unipotentSubgroup)
    (hfac : flagRepresentative i =
      b * weylNF (orbitWeyl k).1 (orbitWeyl k).2 * u) :
    QuotientRowWitness k i := by
  refine ⟨b, hb, ?_⟩
  exact quotientRepresentative_eq_left_smul_of_factorization i b u
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2) hu hfac

theorem exact_factorization_exists_of_quotient_row
    (k : Fin 12) (i : Fin 189) (h : QuotientRowWitness k i) :
    ∃ b u : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧ u ∈ unipotentSubgroup ∧
        flagRepresentative i =
          b * weylNF (orbitWeyl k).1 (orbitWeyl k).2 * u := by
  obtain ⟨b, hb, hq⟩ := h
  obtain ⟨u, hu, hfac⟩ := factorization_of_quotient_witness i b
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2) hq
  exact ⟨b, u, hb, hu, hfac⟩

theorem quotient_row_1_45 : QuotientRowWitness 1 45 := by
  exact ⟨collect (leftFactorWord 1 45), collect_mem_unipotentSubgroup _,
    quotient_witness_cell_one_45⟩

theorem quotient_row_1_73 : QuotientRowWitness 1 73 := by
  exact ⟨collect (leftFactorWord 1 73), collect_mem_unipotentSubgroup _,
    quotient_witness_cell_one_73⟩

theorem quotient_row_1_178 : QuotientRowWitness 1 178 := by
  exact ⟨collect (leftFactorWord 1 178), collect_mem_unipotentSubgroup _,
    quotient_witness_cell_one_178⟩

theorem quotient_row_4_18 : QuotientRowWitness 4 18 := by
  exact ⟨collect (rightFactorWord 4 18), collect_mem_unipotentSubgroup _,
    quotient_witness_cell_four_18⟩

theorem quotient_row_0_0 : QuotientRowWitness 0 0 := by
  refine ⟨collect (leftFactorWord 0 0),
    collect_mem_unipotentSubgroup _, ?_⟩
  exact quotientRepresentative_eq_left_smul_of_factorization 0
    (collect (leftFactorWord 0 0))
    (collect (rightFactorWord 0 0))
    (weylNF (orbitWeyl 0).1 (orbitWeyl 0).2)
    (rightFactorWord_mem_unipotentSubgroup 0 0)
    row_0_0

theorem quotient_row_4_6 : QuotientRowWitness 4 6 := by
  refine ⟨collect (leftFactorWord 4 6),
    collect_mem_unipotentSubgroup _, ?_⟩
  exact quotientRepresentative_eq_left_smul_of_factorization 6
    (collect (leftFactorWord 4 6))
    (collect (rightFactorWord 4 6))
    (weylNF (orbitWeyl 4).1 (orbitWeyl 4).2)
    (rightFactorWord_mem_unipotentSubgroup 4 6)
    row_4_6

theorem quotient_cell_one
    (i : Fin 189) (hi : i ∈ orbitCells 1) :
    QuotientRowWitness 1 i := by
  exact hcell_one i hi

theorem quotient_anchor (k : Fin 12) :
    QuotientRowWitness k (orbitCellAnchor k) := by
  exact hcell_anchor k

theorem quotient_cell_zero
    (i : Fin 189) (hi : i ∈ orbitCells 0) :
    QuotientRowWitness 0 i := by
  have hi0 : i = orbitCellAnchor 0 := by
    simpa [orbitCells, flagCells, orbitCellAnchor] using hi
  subst i
  exact quotient_anchor 0

theorem exact_factorization_exists_cell_one
    (i : Fin 189) (hi : i ∈ orbitCells 1) :
    ∃ b u : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧ u ∈ unipotentSubgroup ∧
        flagRepresentative i =
          b * weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 * u := by
  exact cell_one_factorization_exists i hi

theorem exact_factorization_exists_cell_zero
    (i : Fin 189) (hi : i ∈ orbitCells 0) :
    ∃ b u : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧ u ∈ unipotentSubgroup ∧
        flagRepresentative i =
          b * weylNF (orbitWeyl 0).1 (orbitWeyl 0).2 * u := by
  have hi0 : i = orbitCellAnchor 0 := by
    simpa [orbitCells, flagCells, orbitCellAnchor] using hi
  subst i
  obtain ⟨b, hb, hq⟩ := quotient_anchor 0
  obtain ⟨u, hu, hfac⟩ := factorization_of_quotient_witness
    (orbitCellAnchor 0) b
    (weylNF (orbitWeyl 0).1 (orbitWeyl 0).2) hq
  exact ⟨b, u, hb, hu, hfac⟩

end InfoGeometry.Algebra.Zorn.G2FlagQuotientProvenance
