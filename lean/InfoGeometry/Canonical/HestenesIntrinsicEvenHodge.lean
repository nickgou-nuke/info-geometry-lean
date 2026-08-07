import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Canonical.CliffordParityBridge
import InfoGeometry.Canonical.HestenesBivectorCarrier

namespace InfoGeometry.Canonical.HestenesIntrinsicEvenHodge

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement
open InfoGeometry.Canonical.HestenesBivectorCarrier

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

/-- The intrinsic even Hodge star maps the even subalgebra to itself by
  right multiplication with the volume element. -/
noncomputable def intrinsicEvenHodge : evenOdd Q 0 →ₗ[R] evenOdd Q 0 :=
  sorry

/-- The intrinsic even Hodge star squares to -1 on the even subalgebra. -/
theorem intrinsicEvenHodge_sq (x : evenOdd Q 0) :
    intrinsicEvenHodge R M Q (intrinsicEvenHodge R M Q x) = -x := by
  sorry

end InfoGeometry.Canonical.HestenesIntrinsicEvenHodge
