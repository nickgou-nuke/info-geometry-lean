import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Retired scalar Onsager/Casimir compatibility path

The former coordinate-plane implementation has been removed.  Its
`ℝ × ℝ` gradients and affine reflection were not an Onsager operator on an
observable algebra.  The canonical replacement is
`CasimirHessianFisherBridge`, whose statements use a `CStarAlgebra`, a
positive functional, a native GNS representation, and inner modular
derivations.
-/
