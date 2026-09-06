import InfoGeometry.Canonical.KMSSubstateKMSCondition
import InfoGeometry.Canonical.G2HolonomyGaugeConnections
import InfoGeometry.Canonical.SplitG2StructureOnImaginaryOctonions

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Physics.B3PresentedGroup

/-!
# Super-Kähler modular spinors: quarantine

The imported owners provide the split-octonion carrier, G₂ data, braid action,
and finite KMS readouts separately.  They do not provide a supercharge,
symplectic form, or comparison map satisfying the advertised compatibility
laws.  The former declarations in this file were unsupported `sorry`-based
wrappers (one was even reflexive), so no such API is exported here until those
structures are defined from native algebraic data and their laws are proved.
-/

end InfoGeometry.Canonical
