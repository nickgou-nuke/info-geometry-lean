import Mathlib.Algebra.Group.Units.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Graded twisted-product coherence

This owner isolates the finite cochain mechanism behind a graded
quasi-associative product. A coefficient cochain `F : G → G → Rˣ` defines a
homogeneous product with grade `x + y`; its associator is the coboundary
`∂F`. The file also fixes the concrete grade group `(ZMod 2)^3` and a
standard sign cochain. No identification with the native Zorn product is
asserted here: that is a separate basis-readout theorem.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.Z2ThreeCochainBridge

open scoped BigOperators

variable {R G : Type*} [CommRing R] [AddCommGroup G]

/-- The scalar coefficient of a homogeneous twisted product. -/
def twistedScalar (F : G → G → Rˣ) (x y : G) (a b : R) : R :=
  (F x y : R) * a * b

/-- The associator coefficient attached to a multiplicative two-cochain. -/
def associatorCochain (F : G → G → Rˣ) (x y z : G) : Rˣ :=
  F x y * F (x + y) z * (F y z * F x (y + z))⁻¹

/-- On homogeneous products, reassociation is measured by `∂F`. -/
theorem twistedScalar_associator
    (F : G → G → Rˣ) (x y z : G) (a b c : R) :
    twistedScalar F (x + y) z (twistedScalar F x y a b) c =
      (associatorCochain F x y z : R) *
        twistedScalar F x (y + z) a (twistedScalar F y z b c) := by
  unfold twistedScalar associatorCochain
  simp only [Units.val_mul]
  have hcancel :
      ((F y z * F x (y + z) : Rˣ) : R) *
          (((F y z * F x (y + z))⁻¹ : Rˣ) : R) = 1 := by
    exact (F y z * F x (y + z)).val_inv
  calc
    (F (x + y) z : R) * ((F x y : R) * a * b) * c =
        (F x y : R) * (F (x + y) z : R) * a * b * c := by ring
    _ = (F x y : R) * (F (x + y) z : R) * a * b * c *
          (((F y z * F x (y + z) : Rˣ) : R) *
            (((F y z * F x (y + z))⁻¹ : Rˣ) : R)) := by
          rw [hcancel, mul_one]
    _ = (F x y : R) * (F (x + y) z : R) *
          (((F y z * F x (y + z))⁻¹ : Rˣ) : R) *
          ((F x (y + z) : R) * a * ((F y z : R) * b * c)) := by
      simp only [Units.val_mul]
      ring

/-- The coboundary of a two-cochain satisfies the multiplicative 3-cocycle
identity. -/
theorem associatorCochain_cocycle
    (F : G → G → Rˣ) (x y z w : G) :
    associatorCochain F x y z * associatorCochain F x (y + z) w *
        associatorCochain F y z w =
        associatorCochain F (x + y) z w *
        associatorCochain F x y (z + w) := by
  unfold associatorCochain
  have hxyz : x + (y + z) = (x + y) + z := by ac_rfl
  have hyzw : y + (z + w) = (y + z) + w := by ac_rfl
  rw [hxyz, hyzw]
  let K : Rˣ :=
    F x y * F (x + y) z * F (x + y + z) w *
      (F z w)⁻¹ * (F y (z + w))⁻¹ * (F x (y + (z + w)))⁻¹
  calc
    _ = F x (y + z) * (F x (y + z))⁻¹ *
          F y z * (F y z)⁻¹ * F (y + z) w *
          (F (y + z) w)⁻¹ * K := by
      simp only [K, mul_inv_rev]
      ac_rfl
    _ = K := by simp
    _ = F (x + y) (z + w) * (F (x + y) (z + w))⁻¹ * K := by
      simp
    _ = _ := by
      simp only [K, mul_inv_rev]
      ac_rfl

/-- The finite grade group used by the standard octonionic twisted-group
description. -/
abbrev Z2Grade := Fin 3 → ZMod 2

/-- The sign unit associated to a parity bit. -/
def signUnit (b : ZMod 2) : ℝˣ :=
  if b = 0 then 1 else -1

@[simp] theorem signUnit_zero : signUnit (0 : ZMod 2) = 1 := by
  simp [signUnit]

/-- A concrete sign cochain on `(ZMod 2)^3`. -/
def z2Cochain (x y : Z2Grade) : ℝˣ :=
  signUnit (
    x 0 * y 0 +
      x 1 * y 0 +
      x 1 * y 1 +
      x 2 * y 0 +
      x 2 * y 1 +
      x 2 * y 2 +
      x 1 * y 0 * y 2 +
      x 2 * y 0 * y 1)

abbrev z2Associator (x y z : Z2Grade) : ℝˣ :=
  associatorCochain z2Cochain x y z

theorem z2Associator_cocycle (x y z w : Z2Grade) :
    z2Associator x y z * z2Associator x (y + z) w *
        z2Associator y z w =
      z2Associator (x + y) z w * z2Associator x y (z + w) :=
  associatorCochain_cocycle z2Cochain x y z w

end InfoGeometry.Algebra.Zorn.Z2ThreeCochainBridge
