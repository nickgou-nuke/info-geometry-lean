
import Mathlib.Tactic

/-! This legacy import path retains only the field-valued Zamolodchikov
pentagon recurrence. The finite integer count expressions and their count
updates have a single owner in `InfoGeometry.Canonical.ClusterMutationIndexBridge`;
neither module constructs plabic graphs or derives a graph mutation theorem. -/

namespace PlabicPureBraidMapping

/-! ### Field-valued pentagon recurrence -/

theorem zamolodchikov_cluster_pentagon_period {F : Type*} [Field F]
    (x₀ x₁ : F)
    (h₀ : x₀ ≠ 0) (h₁ : x₁ ≠ 0)
    (h_x₀_add : 1 + x₀ ≠ 0)
    (h_x₁_add : 1 + x₁ ≠ 0)
    (h_sum : 1 + x₀ + x₁ ≠ 0) :
    let x₂ := (1 + x₁) / x₀
    let x₃ := (1 + x₂) / x₁
    let x₄ := (1 + x₃) / x₂
    let x₅ := (1 + x₄) / x₃
    let x₆ := (1 + x₅) / x₄
    x₅ = x₀ ∧ x₆ = x₁ := by
  let x2 := (1 + x₁) / x₀
  let x3 := (1 + x2) / x₁
  let x4 := (1 + x3) / x2
  let x5 := (1 + x4) / x3
  let x6 := (1 + x5) / x4
  change x5 = x₀ ∧ x6 = x₁
  have hsum' : 1 + x₁ + x₀ ≠ 0 := by
    convert h_sum using 1
    ring
  have hx3 : x3 = (1 + x₀ + x₁) / (x₀ * x₁) := by
    change (1 + (1 + x₁) / x₀) / x₁ = _
    field_simp [h₀, h₁]
    ring
  have hx4 : x4 = (1 + x₀) / x₁ := by
    change (1 + x3) / ((1 + x₁) / x₀) = _
    rw [hx3]
    field_simp [h₀, h₁, h_x₁_add]
    ring
  have hx5 : x5 = x₀ := by
    change (1 + x4) / x3 = _
    rw [hx4, hx3]
    field_simp [h₀, h₁, hsum']
    ring
  have hx6 : x6 = x₁ := by
    change (1 + x5) / x4 = _
    rw [hx5, hx4]
    field_simp [h₀, h₁, h_x₀_add]
  exact ⟨hx5, hx6⟩

end PlabicPureBraidMapping
