import Mathlib.Algebra.Group.Basic

namespace InfoGeometry.Physics.Pin

variable {G : Type*} [Group G]

/-- 
A Non-Symmorphic Pin Reflection structure.
The reflection operator R has a double-cover parity.
R flips the translation: R * T = T⁻¹ * R.
-/
def IsPinGlide (R T parity : G) : Prop :=
  R * R = parity ∧
    R * T = T⁻¹ * R ∧
    T⁻¹ * (parity * T) = parity

/-- 
THEOREM: The Pin(5,5) Mandatory Glide Reflection.
Proves that applying the glide reflection (R * T) twice in a non-symmorphic 
lattice completely annihilates the spatial translation, leaving ONLY the 
pure spinor parity of the Pin double-cover.
-/
theorem glide_squared_is_parity (R T parity : G) (h : IsPinGlide R T parity) :
    (R * T) * (R * T) = parity := by
  have hflip : R * T = T⁻¹ * R := h.2.1
  have hsq : R * R = parity := h.1
  calc
    (R * T) * (R * T) = (T⁻¹ * R) * (R * T) := by rw [hflip]
    _ = T⁻¹ * ((R * R) * T) := by simp [mul_assoc]
    _ = T⁻¹ * (parity * T) := by rw [hsq]
    _ = parity := h.2.2

end InfoGeometry.Physics.Pin
