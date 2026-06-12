import Mathlib.Algebra.Group.Basic

namespace InfoGeometry.Physics.Pin

/-- 
The algebraic structure of the Pin(5,5) Glide Reflection.
In a non-symmorphic lattice (like the Klein Bottle boundary of 10D String Theory), 
a reflection R flips the translation parity T. The Glide operator is G = R * T.
-/
variable {G : Type*} [Group G]

/-- 
A Non-Symmorphic Pin Reflection structure.
The reflection operator R has a double-cover parity.
R flips the translation: R * T = T⁻¹ * R.
-/
class IsPinGlide (R T parity : G) : Prop where
  h_R_sq : R * R = parity
  h_flip : R * T = T⁻¹ * R
  h_center : T⁻¹ * (parity * T) = parity

/-- 
THEOREM: The Pin(5,5) Mandatory Glide Reflection.
Proves that applying the glide reflection (R * T) twice in a non-symmorphic 
lattice completely annihilates the spatial translation, leaving ONLY the 
pure spinor parity of the Pin double-cover.
-/
theorem glide_squared_is_parity (R T parity : G) [h : IsPinGlide R T parity] :
    (R * T) * (R * T) = parity := by
  calc (R * T) * (R * T)
    _ = (T⁻¹ * R) * (R * T) := by rw [h.h_flip]
    _ = T⁻¹ * (R * R) * T := by simp [mul_assoc]
    _ = T⁻¹ * parity * T := by rw [h.h_R_sq]
    _ = T⁻¹ * (parity * T) := by simp [mul_assoc]
    _ = parity := by rw [h.h_center]

end InfoGeometry.Physics.Pin
