import InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.AFRecursiveLimitBridge
import InfoGeometry.Canonical.JaynesInductiveLimitBridge
import InfoGeometry.Canonical.JaynesLDDSBridge

/-!
# Jaynes categorical formalism

This export module exposes the native categorical cone and direct-limit
owners together with the concrete Jaynes data packets.  It contains no
duplicate forwarding theorem layer.
-/

namespace InfoGeometry.Canonical.JaynesCategoricalFormalism

export InfoGeometry.Canonical.CategoricalRecursiveClosureBridge (ConeCompatible)
export InfoGeometry.Canonical.AFRecursiveLimitBridge (AFRecursiveLimitPacket)
export InfoGeometry.Canonical.JaynesInductiveLimitBridge (JaynesInductivePacket)
export InfoGeometry.Canonical.JaynesLDDSBridge (JaynesLDDSPacket)

end InfoGeometry.Canonical.JaynesCategoricalFormalism
