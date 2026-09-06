import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate

namespace InfoGeometry.Algebra.Zorn.G2OneCellBruhatCertificate

open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem baseCell_hcell (i : Fin 189) (hi : i ∈ orbitCells 0) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk (weylNF (orbitWeyl 0).1 (orbitWeyl 0).2) :
            SplitOctF2Aut ⧸ unipotentSubgroup) := by
  have hi0 : i = 0 := by
    simpa [orbitCells, flagCells] using hi
  subst i
  refine ⟨1, one_mem _, ?_⟩
  simpa [smul_eq_mul] using (orbitCellAnchor_quotient_eq 0)

end InfoGeometry.Algebra.Zorn.G2OneCellBruhatCertificate
