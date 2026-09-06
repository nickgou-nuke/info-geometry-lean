import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval

namespace InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate

open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def orbitEnum : Fin 189 →
    SplitOctF2Aut ⧸ unipotentSubgroup :=
  quotientRepresentative

/- The GAP exporter uses `correctedC = c⁻¹`; transport to the repository's
   `weylNF` convention therefore reverses the ZMod-6 coordinate. -/
def orbitWeyl : Fin 12 → WeylG2 :=
  fun i => (-((flagWeyl i).1), (flagWeyl i).2)

def orbitCells : Fin 12 → Finset (Fin 189) := flagCells

theorem orbitCells_partition :
    Finset.univ.biUnion orbitCells = Finset.univ := by
  exact flagCells_partition

/- The exporter provides one zero-residual anchor in each cell.  These are
   deliberately recorded as concrete equalities; the non-anchor witnesses
   remain a separate carrier-aligned certificate. -/
def orbitCellAnchor : Fin 12 → Fin 189 :=
  ![0, 24, 3, 9, 6, 15, 1, 16, 7, 10, 4, 25]

set_option maxRecDepth 100000 in
theorem orbitCellAnchor_mem (k : Fin 12) :
    orbitCellAnchor k ∈ orbitCells k := by
  fin_cases k <;> decide

set_option maxRecDepth 100000 in
theorem orbitCellAnchor_eq_weylNF (k : Fin 12) :
    flagRepresentative (orbitCellAnchor k) =
      weylNF (orbitWeyl k).1 (orbitWeyl k).2 := by
  apply autMatrix_injective
  fin_cases k <;> decide

theorem orbitCellAnchor_quotient_eq (k : Fin 12) :
    orbitEnum (orbitCellAnchor k) =
      (QuotientGroup.mk (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
        SplitOctF2Aut ⧸ unipotentSubgroup) := by
  rw [orbitEnum, quotientRepresentative, orbitCellAnchor_eq_weylNF]


end InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
