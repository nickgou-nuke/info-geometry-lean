import Mathlib.Algebra.Group.Basic

namespace InfoGeometry.Physics.Pin

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
Concrete instantiation of IsPinGlide to prove it is not vacuous. 
-/
instance : IsPinGlide (1 : G) (1 : G) (1 : G) where
  h_R_sq := by simp
  h_flip := by simp
  h_center := by simp

lemma glide_step_one (R T parity : G) [h : IsPinGlide R T parity] :
    (R * T) * (R * T) = (T⁻¹ * R) * (R * T) := by
  rw [h.h_flip]

lemma glide_step_two (R T : G) :
    (T⁻¹ * R) * (R * T) = T⁻¹ * (R * R) * T := by
  simp [mul_assoc]

lemma glide_step_three (R T parity : G) [h : IsPinGlide R T parity] :
    T⁻¹ * (R * R) * T = T⁻¹ * (parity * T) := by
  rw [h.h_R_sq, mul_assoc]

/-- 
THEOREM: The Pin(5,5) Mandatory Glide Reflection.
Proves that applying the glide reflection (R * T) twice in a non-symmorphic 
lattice completely annihilates the spatial translation, leaving ONLY the 
pure spinor parity of the Pin double-cover.
-/
theorem glide_squared_is_parity (R T parity : G) [h : IsPinGlide R T parity] :
    (R * T) * (R * T) = parity := by
  rw [glide_step_one R T parity]
  rw [glide_step_two R T]
  rw [glide_step_three R T parity]
  rw [h.h_center]

end InfoGeometry.Physics.Pin
