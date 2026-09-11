import InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate

/-!
# Conditional orbit-membership assembly on `Fin 189`

This owner is a theorem-honest assembly layer: given an explicit
`CellFactorizationCertificate`, it produces quotient-orbit membership for the
requested row. It does not claim a self-contained 189-row proof.
-/

namespace InfoGeometry.Algebra.Zorn.G2Fin189OrbitMembership

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteBruhatOrbitCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagCellFactorizationBridge
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2NativeQuotientRepresentative
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem fin189_orbit_membership
    (C : CellFactorizationCertificate)
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    ∃ b : SplitOctF2Aut,
      b ∈ unipotentSubgroup ∧
      G2FlagOrbitPartitionCertificate.orbitEnum i =
        b • (QuotientGroup.mk
          (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
            G2ConcreteBruhatOrbitCertificate.CarrierQuotient) := by
  refine ⟨collect (C.normalizedLeftFactorWord k i),
    left_factor_mem C k i, ?_⟩
  exact quotientRepresentative_eq_left_smul_of_factorization i
    (collect (C.normalizedLeftFactorWord k i))
    (collect (C.normalizedRightFactorWord k i))
    (weylNF (orbitWeyl k).1 (orbitWeyl k).2)
    (right_factor_mem C k i)
    (factorization_of_mem C k i hi)

theorem concreteBruhatCovering_eq_univ_of_factorization
    (enum : Fin 189 ≃ G2ConcreteBruhatOrbitCertificate.CarrierQuotient)
    (C : CellFactorizationCertificate)
    (henum : ∀ i : Fin 189,
      enum i = G2FlagOrbitPartitionCertificate.orbitEnum i) :
    concreteBruhatCovering = Set.univ := by
  apply covering_eq_univ enum orbitWeyl orbitCells
  · intro k i hi
    obtain ⟨b, hb, hq⟩ := fin189_orbit_membership C k i hi
    refine ⟨b, hb, ?_⟩
    calc
      enum i = G2FlagOrbitPartitionCertificate.orbitEnum i := henum i
      _ = b • (QuotientGroup.mk
        (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :
          G2ConcreteBruhatOrbitCertificate.CarrierQuotient) := hq
  · exact orbitCells_partition

end InfoGeometry.Algebra.Zorn.G2Fin189OrbitMembership
