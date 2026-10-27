import Mathlib.Algebra.Group.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics.Pin

variable {G : Type*} [Group G]

/-- A reflection lift with a reversed translation. The historical name is
retained for compatibility. Here `T` is transverse to the reflection axis;
this hypothesis does not describe the axial translation of a geometric glide. -/
def IsPinGlide (R T parity : G) : Prop :=
  R * R = parity ∧
    R * T = T⁻¹ * R ∧
    T⁻¹ * (parity * T) = parity

/-- For a reversed transverse translation the two translation factors cancel.
This valid group identity is not the square law for a commuting axial glide. -/
theorem glide_squared_is_parity (R T parity : G) (h : IsPinGlide R T parity) :
    (R * T) * (R * T) = parity := by
  have hflip : R * T = T⁻¹ * R := h.2.1
  have hsq : R * R = parity := h.1
  calc
    (R * T) * (R * T) = (T⁻¹ * R) * (R * T) := by rw [hflip]
    _ = T⁻¹ * ((R * R) * T) := by simp [mul_assoc]
    _ = T⁻¹ * (parity * T) := by rw [hsq]
    _ = parity := h.2.2

/-- A commuting axial translation survives the double glide. Fiber parity and
longitudinal translation remain separate factors. -/
theorem axial_glide_squared (R T : G) (h : Commute R T) :
    (R * T) * (R * T) = (R * R) * (T * T) := by
  calc
    (R * T) * (R * T) = R * (T * R) * T := by simp [mul_assoc]
    _ = R * (R * T) * T := by rw [← h.eq]
    _ = (R * R) * (T * T) := by simp [mul_assoc]

end InfoGeometry.Physics.Pin
