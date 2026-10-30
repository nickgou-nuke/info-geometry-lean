/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Group.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics.Pin

variable {G : Type*} [Group G]

/-- A reflection lift with a reversed translation. The historical name is
retained for compatibility. These group hypotheses do not themselves specify
a geometric Pin action. -/
def IsPinGlide (R T parity : G) : Prop :=
  R * R = parity ∧
    R * T = T⁻¹ * R ∧
    T⁻¹ * (parity * T) = parity

/-- Under the reversed-translation and parity-invariance hypotheses, the
translation factors cancel in the square of `R * T`. -/
theorem glide_squared_is_parity (R T parity : G) (h : IsPinGlide R T parity) :
    (R * T) * (R * T) = parity := by
  have hflip : R * T = T⁻¹ * R := h.2.1
  have hsq : R * R = parity := h.1
  calc
    (R * T) * (R * T) = (T⁻¹ * R) * (R * T) := by rw [hflip]
    _ = T⁻¹ * ((R * R) * T) := by simp [mul_assoc]
    _ = T⁻¹ * (parity * T) := by rw [hsq]
    _ = parity := h.2.2

/-- If reflection and translation commute, both factors survive in the square.
This is the algebraic law for a commuting translation; it is separate from the
reversed-translation hypotheses in `IsPinGlide`. -/
theorem axial_glide_squared (R T : G) (h : Commute R T) :
    (R * T) * (R * T) = (R * R) * (T * T) := by
  calc
    (R * T) * (R * T) = R * (T * R) * T := by simp [mul_assoc]
    _ = R * (R * T) * T := by rw [← h.eq]
    _ = (R * R) * (T * T) := by simp [mul_assoc]

end InfoGeometry.Physics.Pin
