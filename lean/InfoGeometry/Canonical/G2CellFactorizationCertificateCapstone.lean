import InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2FlagWordCertificateEval

namespace InfoGeometry.Canonical.G2CellFactorizationCertificateCapstone

open InfoGeometry.Algebra.Zorn.G2CellFactorizationCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

/-- Capstone 2: Verification of G2 Schubert cell factorization certificate. -/
theorem g2_cell_factorization_certificate_canonical_capstone
    (C : CellFactorizationCertificate)
    (k : Fin 12) (i : Fin 189) (hi : i ∈ orbitCells k) :
    flagRepresentative i ∈ concreteBruhatCell (weylNF (orbitWeyl k).1 (orbitWeyl k).2) :=
  representative_mem_concreteBruhatCell C k i hi

end InfoGeometry.Canonical.G2CellFactorizationCertificateCapstone

