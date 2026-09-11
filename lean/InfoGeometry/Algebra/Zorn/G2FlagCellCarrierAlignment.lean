import InfoGeometry.Algebra.Zorn.G2FlagCellWitnessCertificate
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Carrier alignment for the finite G2 flag-cell witness table

The witness tables in `G2FlagCellWitnessCertificate` are retained as data until
they are checked against the current Lean `flagRepresentative` carrier.  This
owner performs exactly that finite check and then transports it through the
native matrix-faithfulness theorem.

No Bruhat-cell disjointness, global coverage, or total Bruhat index is asserted
here.  Those are downstream consequences requiring the complementary reverse
cell-identification / uniqueness step.
-/

namespace InfoGeometry.Algebra.Zorn.G2FlagCellCarrierAlignment

open InfoGeometry.Algebra.Zorn.G2FlagCellWitnessCertificate
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/- The exported witness table is not aligned with the current executable
`flagRepresentative` carrier.  The corresponding finite proposition is false
under `decide`, so this owner intentionally exports no alignment theorem until
the data and carrier are corrected together. -/

end InfoGeometry.Algebra.Zorn.G2FlagCellCarrierAlignment
