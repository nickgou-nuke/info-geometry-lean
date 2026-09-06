import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace InfoGeometry.Categorical

theorem modular_s_inv (τ : ℝ) (h : τ ≠ 0) : - (- τ⁻¹)⁻¹ = τ := by
  field_simp [h]
