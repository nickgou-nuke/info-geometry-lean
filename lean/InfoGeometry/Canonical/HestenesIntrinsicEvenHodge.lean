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
noncomputable def intrinsicEvenHodge (omega_even : Omega (Q := Q) ∈ evenOdd Q 0) : evenOdd Q 0 →ₗ[R] evenOdd Q 0 where
  toFun x := ⟨x.val * Omega (Q := Q), by
    have h := SetLike.mul_mem_graded x.prop omega_even
    rwa [add_zero] at h⟩
  map_add' x y := Subtype.ext (add_mul (x.val) (y.val) (Omega (Q := Q)))
  map_smul' c x := Subtype.ext (Algebra.smul_mul_assoc c x.val (Omega (Q := Q)))

/-- The intrinsic even Hodge star squares to -1 on the even subalgebra. -/

theorem intrinsicEvenHodge_sq (omega_even : Omega (Q := Q) ∈ evenOdd Q 0) (x : evenOdd Q 0) :
    intrinsicEvenHodge R M Q omega_even (intrinsicEvenHodge R M Q omega_even x) = -x := by
  ext
  dsimp [intrinsicEvenHodge]
  rw [mul_assoc, omega_sq, mul_neg, mul_one]

end InfoGeometry.Canonical.HestenesIntrinsicEvenHodge
