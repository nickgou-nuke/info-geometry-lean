import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Canonical.CliffordParityBridge
import InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement
open InfoGeometry.Canonical.HestenesBivectorCarrier

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

-- Assuming we add omega_eq back
axiom omega_eq : Omega (R := R) (M := M) (Q := Q) = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)
