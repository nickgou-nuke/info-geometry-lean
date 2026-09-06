import InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
import InfoGeometry.Algebra.Zorn.G2FlagFactorizationNormalizedData
import InfoGeometry.Algebra.Zorn.G2FlagFactorizationOrientation

namespace InfoGeometry.Canonical.G2CellFactorizationCapstone

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/--
🏆 CAPSTONE THEOREM: G₂ Schubert Cell Factorization Canonical Instantiation.
Verifies that any `CellFactorizationCertificate`:
1. Left unipotent factor belongs to `unipotentSubgroup`.
2. Right unipotent factor belongs to `unipotentSubgroup`.
3. The flag representative factors into unipotent · Weyl · unipotent.
4. The flag representative lies in the concrete Bruhat cell.
-/
theorem g2_cell_factorization_canonical_capstone
    (C : CellFactorizationCertificate)
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    -- 1. Left unipotent factor membership
    collect (C.normalizedLeftFactorWord k i) ∈ unipotentSubgroup ∧
    -- 2. Right unipotent factor membership
    collect (C.normalizedRightFactorWord k i) ∈ unipotentSubgroup ∧
    -- 3. Exact factorization formula
    flagRepresentative i =
      collect (C.normalizedLeftFactorWord k i) *
        weylNF (orbitWeyl k).1 (orbitWeyl k).2 *
          collect (C.normalizedRightFactorWord k i) ∧
    -- 4. Concrete Bruhat cell containment
    flagRepresentative i ∈ concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2) := by
  refine ⟨left_factor_mem C k i, right_factor_mem C k i, factorization_of_mem C k i hi, representative_mem_concreteBruhatCell C k i hi⟩

end InfoGeometry.Canonical.G2CellFactorizationCapstone
