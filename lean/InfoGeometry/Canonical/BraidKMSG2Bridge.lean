import InfoGeometry.Canonical.BraidKMSCompatibility
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.QuantumKMSSymmetricSpace
import InfoGeometry.Canonical.G2HolonomyGaugeConnections
import InfoGeometry.Canonical.SplitG2StructureOnImaginaryOctonions
import InfoGeometry.Canonical.SplitOctonionColorS3Automorphisms

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Physics.B3PresentedGroup

/-!
# Braid-KMS to G₂ bridge quarantine

The imported owners expose the braid action, the finite KMS readout, and the
split-G₂ structures independently.  They do not yet expose a map from braid
generators to G₂ automorphisms, nor a KMS-preserving algebra homomorphism.  The
former declarations in this file used `sorry` for precisely those missing
maps and stated conclusions unrelated to their hypotheses.  No bridge claim
is exported until those comparison maps are constructed and proved.
-/

end InfoGeometry.Canonical
