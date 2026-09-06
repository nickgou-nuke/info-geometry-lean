import InfoGeometry.Canonical.RelativeSurprisalRadonNikodymBridge
import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge

/-!
# Retired scalar Gaussian/Möbius information surface

The former `GaussianMean2D` implementation used a Euclidean distance between
two real records and named it KL divergence.  No Gaussian measure, density,
Radon--Nikodym derivative, or observable-algebra operator was present, so the
surface was a scalar toy rather than an information-geometric theorem.

The finite noncommutative replacement is the relative modular operator and its
negative-log potential, together with positive-functional/GNS Fisher readouts
in `CasimirHessianFisherBridge`.  This compatibility file intentionally exports
no scalar KL, free-energy, or critical-line API.
-/

namespace InfoGeometry.SuperMetriplectic.MoebiusGaussian

end InfoGeometry.SuperMetriplectic.MoebiusGaussian
