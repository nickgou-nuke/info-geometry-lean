import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.QuaternionChiralCone

Noncommutative quaternion geometry with a symmetry-adapted chiral axis chart.

Choose `î = (0,1,0,0)` and define `z(τ, χ) = τ•1 + χ•î`.
This 2D slice is closed under multiplication and commutative, while ambient
quaternion multiplication is noncommutative.
-/

namespace InfoGeometry.Canonical.QuaternionChiralCone

open Quaternion

section

variable {R : Type*} [CommRing R]

/-- Chiral axis unit `î`. -/
def iHat : Quaternion R := ⟨0, 1, 0, 0⟩

/-- Symmetry-adapted chiral chart coordinate. -/
def chiralCoord (τ χ : R) : Quaternion R :=
  τ • (1 : Quaternion R) + χ • iHat

@[simp] theorem chiralCoord_re (τ χ : R) : (chiralCoord (R := R) τ χ).re = τ := by
  simp [chiralCoord, iHat]

@[simp] theorem chiralCoord_imI (τ χ : R) : (chiralCoord (R := R) τ χ).imI = χ := by
  simp [chiralCoord, iHat]

@[simp] theorem chiralCoord_imJ (τ χ : R) : (chiralCoord (R := R) τ χ).imJ = 0 := by
  simp [chiralCoord, iHat]

@[simp] theorem chiralCoord_imK (τ χ : R) : (chiralCoord (R := R) τ χ).imK = 0 := by
  simp [chiralCoord, iHat]

/-- Closed multiplication law on the chiral axis chart. -/
theorem chiralCoord_mul (τ₁ χ₁ τ₂ χ₂ : R) :
    chiralCoord (R := R) τ₁ χ₁ * chiralCoord (R := R) τ₂ χ₂ =
      chiralCoord (R := R) (τ₁ * τ₂ - χ₁ * χ₂) (τ₁ * χ₂ + χ₁ * τ₂) := by
  ext <;> simp [chiralCoord, iHat, mul_comm, sub_eq_add_neg]

/-- Commutativity recovered on the fixed-axis chiral slice. -/
theorem chiralCoord_mul_comm (τ₁ χ₁ τ₂ χ₂ : R) :
    chiralCoord (R := R) τ₁ χ₁ * chiralCoord (R := R) τ₂ χ₂ =
      chiralCoord (R := R) τ₂ χ₂ * chiralCoord (R := R) τ₁ χ₁ := by
  rw [chiralCoord_mul, chiralCoord_mul]
  simp [mul_comm, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

/-- Pure-axis line is additive in the scalar parameter. -/
theorem pureAxis_add (x y : R) :
    ((x + y) • iHat : Quaternion R) = (x : R) • iHat + y • iHat := by
  simp [add_smul]

end

end InfoGeometry.Canonical.QuaternionChiralCone
