import InfoGeometry.Algebra.Zorn.G2FlagFactorizationRecursion
import InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure

namespace InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

abbrev NormalizedFactorWord :=
  Fin 12 → Fin 189 → G2CanonicalPCCollector.FactorWord

structure CellFactorizationCertificate where
  normalizedLeftFactorWord : NormalizedFactorWord
  normalizedRightFactorWord : NormalizedFactorWord
  sound : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
    flagRepresentative i =
      collect (normalizedLeftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (normalizedRightFactorWord k i)

theorem factorization_of_mem
    (C : CellFactorizationCertificate)
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i =
      collect (C.normalizedLeftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (C.normalizedRightFactorWord k i) :=
  C.sound k i hi

theorem left_factor_mem
    (C : CellFactorizationCertificate)
    (k : Fin 12) (i : Fin 189) :
    collect (C.normalizedLeftFactorWord k i) ∈ unipotentSubgroup :=
  collect_mem_unipotentSubgroup _

theorem right_factor_mem
    (C : CellFactorizationCertificate)
    (k : Fin 12) (i : Fin 189) :
    collect (C.normalizedRightFactorWord k i) ∈ unipotentSubgroup :=
  collect_mem_unipotentSubgroup _

theorem representative_mem_concreteBruhatCell
    (C : CellFactorizationCertificate)
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i ∈
      concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2) := by
  exact flagRepresentative_mem_concreteBruhatCell_of_factorization i
    (collect (C.normalizedLeftFactorWord k i))
    (collect (C.normalizedRightFactorWord k i))
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2)
    (left_factor_mem C k i) (right_factor_mem C k i)
    (factorization_of_mem C k i hi)

/--
Construct a `CellFactorizationCertificate` from normalized left/right word maps and a soundness witness.
-/
def ofWords
    (left : NormalizedFactorWord)
    (right : NormalizedFactorWord)
    (hsound : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i =
        collect (left k i) *
          weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
            collect (right k i)) :
    CellFactorizationCertificate where
  normalizedLeftFactorWord := left
  normalizedRightFactorWord := right
  sound := hsound

/--
Standard forward-order constructor using the canonical left/right factor words.
-/
def ofForwardWords
    (hsound : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i =
        collect (leftFactorWord k i) *
          weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
            collect (rightFactorWord k i)) :
    CellFactorizationCertificate where
  normalizedLeftFactorWord := leftFactorWord
  normalizedRightFactorWord := rightFactorWord
  sound := hsound

end InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
