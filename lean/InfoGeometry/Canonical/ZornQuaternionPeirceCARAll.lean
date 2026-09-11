import InfoGeometry.Canonical.ZornQuaternionPeirceCAR
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornQuaternionPeirceCARPristineChain
import InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope

/-!
# Focused aggregate for the Zorn, derivation, CAR, and CCR reconstruction

This module exports three distinct mathematical layers:

* the nonassociative split-octonion Zorn multiplication;
* its Lie algebra of Leibniz derivations under endomorphism commutator;
* associative doubled/countable operator envelopes carrying exact CAR and CCR.

The ambient Zorn nonassociativity is not used as a restriction on the operator
or derivation conclusions. The transitive axiom audit remains a separate
executable target.
-/
