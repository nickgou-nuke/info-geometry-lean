import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Canonical.CliffordParityBridge
import InfoGeometry.Canonical.HestenesBivectorCarrier

namespace InfoGeometry.Canonical.HestenesTransportedOddHodge

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement
open InfoGeometry.Canonical.HestenesBivectorCarrier

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

/-- The transported odd Hodge star maps the odd subalgebra to itself.
    It is defined as R_{gamma_0} ∘ star ∘ R_{gamma_0}^{-1}. -/
noncomputable def transportedOddHodge : evenOdd Q 1 →ₗ[R] evenOdd Q 1 :=
  sorry

/-- The transported odd Hodge star squares to +1 on the odd subalgebra. -/
theorem transportedOddHodge_sq (x : evenOdd Q 1) :
    transportedOddHodge R M Q (transportedOddHodge R M Q x) = x := by
  sorry

/-- The canonical identity connecting transported odd Hodge to intrinsic even Hodge. -/
theorem transported_eq_intrinsic_adjoint (y : evenOdd Q 0) :
    (transportedOddHodge R M Q ⟨y.val * ι Q (HasSpacetimeBasis.gamma Q 0), sorry⟩).val = 
      -(CliffordAlgebra.reverse (y.val)) * Omega (Q := Q) := by
  sorry

/-- The transported odd Hodge star maps self-adjoint elements to skew-adjoint elements. -/
theorem transportedOddHodge_selfAdjoint (y : evenOdd Q 1) (hy : CliffordAlgebra.reverse y.val = y.val) :
    CliffordAlgebra.reverse (transportedOddHodge R M Q y).val = -(transportedOddHodge R M Q y).val := by
  sorry

/-- The transported odd Hodge star maps skew-adjoint elements to self-adjoint elements. -/
theorem transportedOddHodge_skewAdjoint (y : evenOdd Q 1) (hy : CliffordAlgebra.reverse y.val = -y.val) :
    CliffordAlgebra.reverse (transportedOddHodge R M Q y).val = (transportedOddHodge R M Q y).val := by
  sorry

end InfoGeometry.Canonical.HestenesTransportedOddHodge
