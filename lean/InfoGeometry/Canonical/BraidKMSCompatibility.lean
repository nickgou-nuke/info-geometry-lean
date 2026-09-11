import InfoGeometry.Canonical.BraidPermutationActionOnCuntzFamily
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzGeneratorKMSLogThree
import InfoGeometry.Canonical.CuntzWordMonomialKMSFunctional
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Physics.B3PresentedGroup

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Physics.B3PresentedGroup

/-!
# Braid-KMS compatibility quarantine

The imported files provide the finite word-level braid action and the generator
KMS readouts separately.  They do not currently provide a KMS-preserving
automorphism of the Cuntz algebra.  In particular, the former claims in this
file related an arbitrary word image to unrelated words or treated a left-word
action as an algebra automorphism.  Those claims are therefore intentionally
not stated until the missing preservation hypotheses are formalized.
-/

end InfoGeometry.Canonical
