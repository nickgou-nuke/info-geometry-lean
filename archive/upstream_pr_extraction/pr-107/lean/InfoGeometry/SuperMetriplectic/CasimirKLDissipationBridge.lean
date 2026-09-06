import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge

/-!
# Retired scalar Casimir/KL dissipation path

The former implementation was an explicit ODE for a quadratic function of two
real coordinates.  It did not define a Poisson algebra, an Onsager operator,
or a Radon--Nikodym/KL construction, so its contraction statements were not
the requested noncommutative geometry.

The maintained replacement is `CasimirHessianFisherBridge`: it uses a genuine
`CStarAlgebra`, a verified quadratic Casimir, inner modular derivations, a
positive functional, and its native GNS realization.  This compatibility
module intentionally exports no scalar theorem surface.
-/
