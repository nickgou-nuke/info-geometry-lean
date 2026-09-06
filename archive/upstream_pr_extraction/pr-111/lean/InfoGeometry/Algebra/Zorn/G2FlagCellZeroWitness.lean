import InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness

namespace InfoGeometry.Algebra.Zorn.G2FlagCellZeroWitness

open InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem hcell_zero (i : Fin 189) (hi : i ∈ orbitCells 0) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
        orbitEnum i = b •
          (QuotientGroup.mk
            (weylNF (orbitWeyl 0).1 (orbitWeyl 0).2) :
              InfoGeometry.Algebra.Zorn.G2FlagCellQuotientWitness.CarrierQuotient) := by
  have hi0 : i = orbitCellAnchor 0 := by
    simpa [orbitCells, flagCells, orbitCellAnchor] using hi
  subst i
  exact hcell_anchor 0

end InfoGeometry.Algebra.Zorn.G2FlagCellZeroWitness
