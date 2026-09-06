import InfoGeometry.SuperMetriplectic.Flow
import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge
import InfoGeometry.Canonical.MetriplecticJacobianDecompositionBridge

/-!
# Compatibility surface for the operatorial Souriau/Onsager lane

The former owner encoded dissipation as `u^2 * Q` on a scalar chart.  That is
only a coordinate shadow and is not the framework's Onsager object.  The
native route is the observable-algebra Onsager flow and its positive
functional, with Jacobian production handled by the operatorial cocycle owner.
-/
