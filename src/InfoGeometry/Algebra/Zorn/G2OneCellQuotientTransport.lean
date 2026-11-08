import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeCoverage

namespace InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2BNPair
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2QuotientRepresentativeCoverage
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem cell_one_quotient_witness
    (i : Fin 189) :
    (hfac : flagRepresentative i =
      collect (leftFactorWord 1 i) *
        weylNF (orbitWeyl 1).1 (orbitWeyl 1).2 *
        collect (rightFactorWord 1 i)) →
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        quotientRepresentative i =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl 1).1 (orbitWeyl 1).2) :
              G2FlagCellQuotientWitness.CarrierQuotient) := by
  intro hfac
  exact quotient_orbit_witness_of_collected_factorization 1 i hfac

theorem all_cells_quotient_witness
    (k : Fin 12) (i : Fin 189) :
    (hfac : flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (rightFactorWord k i)) →
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        quotientRepresentative i =
          b • (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
              G2FlagCellQuotientWitness.CarrierQuotient) := by
  intro hfac
  exact quotient_orbit_witness_of_collected_factorization k i hfac

theorem all_cells_orbitEnum_hcell
    (k : Fin 12) (i : Fin 189) :
    (hfac : flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (rightFactorWord k i)) →
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
              G2FlagCellQuotientWitness.CarrierQuotient) := by
  intro hfac
  exact all_cells_quotient_witness k i hfac

theorem all_cells_representative_mem
    (k : Fin 12) (i : Fin 189) :
    (hfac : flagRepresentative i =
      collect (leftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (rightFactorWord k i)) →
    flagRepresentative i ∈
      concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2) := by
  intro hfac
  rw [concreteBruhatCell_eq_exact_unipotentCell]
  apply (mem_doubleCoset_iff_quotient_smul
    unipotentSubgroup
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2)
    (flagRepresentative i)).2
  obtain ⟨b, hb, hq⟩ := all_cells_quotient_witness k i hfac
  exact ⟨b, hb, hq.symm⟩

end InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport
