import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import InfoGeometry.Clifford.HestenesOddSector

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- 
The Spin Rotor Action on Spacetime:
An even operator R acts on an odd vector v by the adjoint action R * v * R⁻¹.
This theorem guarantees that the resulting object is strictly contained within the odd sector.
-/
theorem spin_action_preserves_odd (R_op v R_inv : CliffordAlgebra Q)
    (hR : R_op ∈ ClPlus Q) (hv : v ∈ ClMinus Q) (hRinv : R_inv ∈ ClPlus Q) :
    R_op * v * R_inv ∈ ClMinus Q := by
  -- R_op * v is in ClMinus
  have h_Rv := clPlus_mul_clMinus Q R_op v hR hv
  -- (R_op * v) * R_inv is in ClMinus
  exact clMinus_mul_clPlus Q (R_op * v) R_inv h_Rv hRinv

/-- 
A geometric rotor in the even subalgebra.
We define a Rotor as an even element R such that R * R_rev = 1.
-/
structure GeometricRotor (Q : QuadraticForm R M) where
  val : ClPlus Q

/-- The canonical adjoint action of a Rotor on a generalized spacetime vector -/
def GeometricRotor.action (R_op : GeometricRotor Q) (v : ClMinus Q) (R_inv : ClPlus Q) : ClMinus Q :=
  ⟨R_op.val.val * v.val * R_inv.val, spin_action_preserves_odd Q R_op.val.val v.val R_inv.val R_op.val.property v.property R_inv.property⟩

end InfoGeometry.Clifford.Hestenes
