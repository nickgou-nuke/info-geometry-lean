import InfoGeometry.Algebra.Zorn.G2FlagFactorizationOrientation
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2FlagFactorizationNormalizedData

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagFactorizationOrientation
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

structure Data where
  reversed : Fin 12 → Fin 189 → Bool

noncomputable def left (D : Data) (k : Fin 12) (i : Fin 189) : FactorWord :=
  normalizedLeftFactorWord k i (D.reversed k i)

noncomputable def right (D : Data) (k : Fin 12) (i : Fin 189) : FactorWord :=
  normalizedRightFactorWord k i (D.reversed k i)

theorem sound
    (D : Data)
    (hraw : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i =
        if D.reversed k i then
          collect (rightFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (leftFactorWord k i)
        else
          collect (leftFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (rightFactorWord k i))
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i =
      collect (left D k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (right D k i) := by
  exact normalizedFactorization_of_orientation_certificate k i
    (D.reversed k i) (hraw k i hi)

theorem left_mem (D : Data) (k : Fin 12) (i : Fin 189) :
    collect (left D k i) ∈ unipotentSubgroup := by
  exact normalizedLeftFactorWord_mem_unipotentSubgroup k i (D.reversed k i)

theorem right_mem (D : Data) (k : Fin 12) (i : Fin 189) :
    collect (right D k i) ∈ unipotentSubgroup := by
  exact normalizedRightFactorWord_mem_unipotentSubgroup k i (D.reversed k i)

noncomputable def toCellFactorizationCertificate
    (D : Data)
    (hraw : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i =
        if D.reversed k i then
          collect (rightFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (leftFactorWord k i)
        else
          collect (leftFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (rightFactorWord k i)) :
    CellFactorizationCertificate where
  normalizedLeftFactorWord := left D
  normalizedRightFactorWord := right D
  sound := sound D hraw

theorem factorization_of_data
    (D : Data)
    (hraw : ∀ (k : Fin 12) (i : Fin 189), i ∈ orbitCells k →
      flagRepresentative i =
        if D.reversed k i then
          collect (rightFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (leftFactorWord k i)
        else
          collect (leftFactorWord k i) *
            weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
              collect (rightFactorWord k i))
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i =
      collect (left D k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (right D k i) := by
  exact sound D hraw k i hi

end InfoGeometry.Algebra.Zorn.G2FlagFactorizationNormalizedData
