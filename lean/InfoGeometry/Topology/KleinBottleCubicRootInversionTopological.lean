import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

/-!
# Cubic-root inversion in the Klein-bottle monodromy lane

The orientation-reversing generator acts on a cubic cyclotomic parameter by
inversion.  For a cube root this is the square, and the corresponding colour
charge becomes the square of the original charge.  The statements are made
on the discrete root subtype and use the native finite linear operators.
-/

namespace InfoGeometry.Topology.KleinBottleCubicRootInversionTopological

open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

noncomputable section

/-- Inversion on the cubic-root parameter set. -/
noncomputable def cubicRootInversion :
    CubicRootParameter ≃ₜ CubicRootParameter where
  toFun q := ⟨q.1 ^ 2, by
    calc
      (q.1 ^ 2) ^ 3 = (q.1 ^ 3) ^ 2 := by ring
      _ = 1 := by rw [q.2]; norm_num⟩
  invFun q := ⟨q.1 ^ 2, by
    calc
      (q.1 ^ 2) ^ 3 = (q.1 ^ 3) ^ 2 := by ring
      _ = 1 := by rw [q.2]; norm_num⟩
  left_inv q := by
    apply Subtype.ext
    change (q.1 ^ 2) ^ 2 = q.1
    have h4 : q.1 ^ 4 = q.1 := by
      calc
        q.1 ^ 4 = q.1 ^ 3 * q.1 := by ring
        _ = q.1 := by rw [q.2]; simp
    calc
      (q.1 ^ 2) ^ 2 = q.1 ^ 4 := by ring
      _ = q.1 := h4
  right_inv q := by
    apply Subtype.ext
    change (q.1 ^ 2) ^ 2 = q.1
    have h4 : q.1 ^ 4 = q.1 := by
      calc
        q.1 ^ 4 = q.1 ^ 3 * q.1 := by ring
        _ = q.1 := by rw [q.2]; simp
    calc
      (q.1 ^ 2) ^ 2 = q.1 ^ 4 := by ring
      _ = q.1 := h4
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

@[simp] theorem cubicRootInversion_apply (q : CubicRootParameter) :
    cubicRootInversion q = ⟨q.1 ^ 2, by
      calc
        (q.1 ^ 2) ^ 3 = (q.1 ^ 3) ^ 2 := by ring
        _ = 1 := by rw [q.2]; norm_num⟩ := by
  rfl

theorem cubicRootChargeReadout_inversion
    (q : CubicRootParameter) :
    cubicRootChargeReadout (cubicRootInversion q) =
      (cubicRootChargeReadout q).comp (cubicRootChargeReadout q) := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i
  · rfl
  · change q.1 ^ 2 * v 1 = q.1 * (q.1 * v 1)
    ring
  · change (q.1 ^ 2) ^ 2 * v 2 =
      q.1 ^ 2 * (q.1 ^ 2 * v 2)
    ring

end
end InfoGeometry.Topology.KleinBottleCubicRootInversionTopological
