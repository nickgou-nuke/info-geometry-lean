import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Arithmetic zeta product gates

Small reusable gate layer for product conditions extracted from arithmetic
symmetry packets.

`ProductZeroGate` records a finite product-annihilation condition.  A separate
`ProductUnitGate` records the lossless/unit condition.  The split prevents the
common wording error of calling a product equal to `1` a product-zero gate.
No zeta analytic continuation, zero-location theorem, or spectral statement is
asserted here.
-/

namespace InfoGeometry.Arithmetic.ZetaGate

/-- Abstract product-zero gate over two scalar readouts. -/
structure ProductZeroGate (H : Type*) where
  Z_boson : H → ℂ
  Z_fermion : H → ℂ
  h_product_zero : ∀ x : H, Z_boson x * Z_fermion x = 0

namespace ProductZeroGate

variable {H : Type*} (gate : ProductZeroGate H)

/-- The product-zero gate annihilates the paired product. -/
theorem product_eq_zero (x : H) :
    gate.Z_boson x * gate.Z_fermion x = 0 :=
  gate.h_product_zero x

/-- Reversed order also vanishes over the commutative scalar field. -/
theorem product_comm_eq_zero (x : H) :
    gate.Z_fermion x * gate.Z_boson x = 0 := by
  simpa [mul_comm] using gate.product_eq_zero x

end ProductZeroGate

/-- Abstract product-unit gate over two scalar readouts. -/
structure ProductUnitGate (H : Type*) where
  Z_left : H → ℂ
  Z_right : H → ℂ
  h_product_unit : ∀ x : H, Z_left x * Z_right x = 1

namespace ProductUnitGate

variable {H : Type*} (gate : ProductUnitGate H)

/-- The product-unit gate is lossless in the recorded direction. -/
theorem product_eq_one (x : H) :
    gate.Z_left x * gate.Z_right x = 1 :=
  gate.h_product_unit x

/-- Reversed order is also unit over the commutative scalar field. -/
theorem product_comm_eq_one (x : H) :
    gate.Z_right x * gate.Z_left x = 1 := by
  simpa [mul_comm] using gate.product_eq_one x

end ProductUnitGate

/-- Combined readout for independent zero and unit gates on the same carrier. -/
theorem product_gate_readout {H : Type*}
    (zeroGate : ProductZeroGate H) (unitGate : ProductUnitGate H) (x : H) :
    zeroGate.Z_boson x * zeroGate.Z_fermion x = 0 ∧
      unitGate.Z_left x * unitGate.Z_right x = 1 :=
  ⟨zeroGate.product_eq_zero x, unitGate.product_eq_one x⟩

end InfoGeometry.Arithmetic.ZetaGate
