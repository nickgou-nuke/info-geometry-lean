import InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
import InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
import InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
import InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
import InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

/-!
# Native readback interface for GAP flag witnesses

The witness tables are data. This file contains only the structural lift from
an explicit native matrix equality to a group factorization and a quotient
witness. It does not assert matrix soundness for the imported data, and it is
not an all-row factorization theorem.
-/

namespace InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessReadback

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessData
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def gapWitnessMatrixSound (k : Fin 12) (i : Fin 189) : Prop :=
  autMatrix (flagRepresentative i) =
    autMatrix
      (collect (gapLeftWitness k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (gapRightWitness k i))

theorem gapWitness_group_factorization
    (k : Fin 12) (i : Fin 189)
    (h : gapWitnessMatrixSound k i) :
    flagRepresentative i =
      collect (gapLeftWitness k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
        collect (gapRightWitness k i) := by
  exact autMatrix_injective h

theorem gapWitness_quotient_orbit
    (k : Fin 12) (i : Fin 189)
    (h : gapWitnessMatrixSound k i) :
    quotientRepresentative i =
      collect (gapLeftWitness k i) •
        (QuotientGroup.mk
          (weylNF (orbitWeyl k).1 (orbitWeyl k).2) : CarrierQuotient) := by
  exact quotientRepresentative_eq_left_smul_of_factorization i
    (collect (gapLeftWitness k i))
    (collect (gapRightWitness k i))
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2)
    (gapRightWitness_mem_unipotentSubgroup k i)
    (gapWitness_group_factorization k i h)

theorem quotientRowWitness_of_all_gapWitness_matrix_sound
    (hmat : ∀ (k : Fin 12) (i : Fin 189),
      i ∈ orbitCells k → gapWitnessMatrixSound k i) :
    ∀ (k : Fin 12) (i : Fin 189),
      i ∈ orbitCells k →
        ∃ b : SplitOctF2Aut,
          b ∈ unipotentSubgroup ∧
            orbitEnum i = b •
              (QuotientGroup.mk
                (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
                CarrierQuotient) := by
  intro k i hi
  refine ⟨collect (gapLeftWitness k i),
    gapLeftWitness_mem_unipotentSubgroup k i, ?_⟩
  exact gapWitness_quotient_orbit k i (hmat k i hi)

end InfoGeometry.Algebra.Zorn.G2GAPFlagWitnessReadback
