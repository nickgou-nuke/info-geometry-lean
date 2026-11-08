import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

namespace InfoGeometry.PlabicCluster

variable {F : Type*} [Field F]

/-! ### 1. Cluster Face Weights around a Plabic Square Face -/

/-- The 5 face weights in the local neighborhood of a plabic square face:
    - `yf`: central square face f
    - `y1`, `y3`: adjacent faces with incoming quiver arrows from f
    - `y2`, `y4`: adjacent faces with outgoing quiver arrows to f -/
@[ext]
structure SquareFaceWeights (F : Type*) where
  yf : F
  y1 : F
  y2 : F
  y3 : F
  y4 : F

/-- Cluster X-mutation at the central face f:
    yf' = yf⁻¹
    y₁' = y₁ * (1 + yf)
    y₂' = y₂ * (1 + yf⁻¹)⁻¹
    y₃' = y₃ * (1 + yf)
    y₄' = y₄ * (1 + yf⁻¹)⁻¹ -/
def mutateF (w : SquareFaceWeights F) : SquareFaceWeights F where
  yf := w.yf⁻¹
  y1 := w.y1 * (1 + w.yf)
  y2 := w.y2 * (1 + w.yf⁻¹)⁻¹
  y3 := w.y3 * (1 + w.yf)
  y4 := w.y4 * (1 + w.yf⁻¹)⁻¹

/-- Reversed cluster mutation at f' (with all quiver arrows reversed at f):
    yf'' = yf'⁻¹
    y₁'' = y₁' * (1 + yf'⁻¹)⁻¹
    y₂'' = y₂' * (1 + yf')
    y₃'' = y₃' * (1 + yf'⁻¹)⁻¹
    y₄'' = y₄' * (1 + yf') -/
def mutateF_rev (w : SquareFaceWeights F) : SquareFaceWeights F where
  yf := w.yf⁻¹
  y1 := w.y1 * (1 + w.yf⁻¹)⁻¹
  y2 := w.y2 * (1 + w.yf)
  y3 := w.y3 * (1 + w.yf⁻¹)⁻¹
  y4 := w.y4 * (1 + w.yf)

/-! ### 2. Rational Simplification of Adjacent Denominators -/

/-- Lemma: (1 + y⁻¹) ≠ 0 whenever y ≠ 0 and 1 + y ≠ 0. -/
lemma one_add_inv_ne_zero (y : F) (hy : y ≠ 0) (h_add : 1 + y ≠ 0) :
    1 + y⁻¹ ≠ 0 := by
  intro h
  apply h_add
  have : y * (1 + y⁻¹) = 0 := by rw [h, mul_zero]
  rw [mul_add, mul_one, mul_inv_cancel₀ hy, add_comm] at this
  exact this

/-- Lemma: (1 + y⁻¹)⁻¹ = y * (1 + y)⁻¹. -/
lemma inv_one_add_inv (y : F) (hy : y ≠ 0) (h_add : 1 + y ≠ 0) :
    (1 + y⁻¹)⁻¹ = y * (1 + y)⁻¹ := by
  have h1 : (1 + y⁻¹) * (y * (1 + y)⁻¹) = 1 := by
    have hy_distrib : (1 + y⁻¹) * y = 1 + y := by
      calc (1 + y⁻¹) * y = 1 * y + y⁻¹ * y := by rw [add_mul]
        _ = y + 1 := by rw [one_mul, inv_mul_cancel₀ hy]
        _ = 1 + y := by rw [add_comm]
    calc (1 + y⁻¹) * (y * (1 + y)⁻¹)
        = ((1 + y⁻¹) * y) * (1 + y)⁻¹ := by rw [mul_assoc]
      _ = (1 + y) * (1 + y)⁻¹ := by rw [hy_distrib]
      _ = 1 := mul_inv_cancel₀ h_add
  have h_ne := one_add_inv_ne_zero y hy h_add
  calc (1 + y⁻¹)⁻¹ = (1 + y⁻¹)⁻¹ * 1 := by rw [mul_one]
    _ = (1 + y⁻¹)⁻¹ * ((1 + y⁻¹) * (y * (1 + y)⁻¹)) := by rw [h1]
    _ = ((1 + y⁻¹)⁻¹ * (1 + y⁻¹)) * (y * (1 + y)⁻¹) := by rw [mul_assoc]
    _ = 1 * (y * (1 + y)⁻¹) := by rw [inv_mul_cancel₀ h_ne]
    _ = y * (1 + y)⁻¹ := by rw [one_mul]

/-! ### 3. Fundamental Properties of Plabic Urban Renewal -/

/-- Master Theorem 1 (Central Face Inversion):
    The central face weight is strictly inverted under the square move:
    (y_f') = y_f⁻¹. -/
theorem square_move_central_inversion (w : SquareFaceWeights F) :
    (mutateF w).yf = w.yf⁻¹ :=
  rfl

/-- Master Theorem 2A (Opposite Pair 1-2 Scaling):
    The product of opposite face weights y₁' * y₂' scales by y_f:
    y₁' * y₂' = y₁ * y₂ * y_f. -/
theorem square_move_opposite_pair_12 (w : SquareFaceWeights F)
    (hyf : w.yf ≠ 0) (h_add : 1 + w.yf ≠ 0) :
    (mutateF w).y1 * (mutateF w).y2 = w.y1 * w.y2 * w.yf := by
  dsimp [mutateF]
  rw [inv_one_add_inv w.yf hyf h_add]
  have h_cancel : (1 + w.yf) * (w.yf * (1 + w.yf)⁻¹) = w.yf := by
    calc (1 + w.yf) * (w.yf * (1 + w.yf)⁻¹)
        = (1 + w.yf) * ((1 + w.yf)⁻¹ * w.yf) := by rw [mul_comm w.yf]
      _ = ((1 + w.yf) * (1 + w.yf)⁻¹) * w.yf := by rw [← mul_assoc]
      _ = 1 * w.yf := by rw [mul_inv_cancel₀ h_add]
      _ = w.yf := one_mul w.yf
  calc (w.y1 * (1 + w.yf)) * (w.y2 * (w.yf * (1 + w.yf)⁻¹))
      = (w.y1 * w.y2) * ((1 + w.yf) * (w.yf * (1 + w.yf)⁻¹)) := by ring
    _ = (w.y1 * w.y2) * w.yf := by rw [h_cancel]
    _ = w.y1 * w.y2 * w.yf := by rw [mul_assoc]

/-- Master Theorem 2B (Opposite Pair 3-4 Scaling):
    The product of opposite face weights y₃' * y₄' scales by y_f:
    y₃' * y₄' = y₃ * y₄ * y_f. -/
theorem square_move_opposite_pair_34 (w : SquareFaceWeights F)
    (hyf : w.yf ≠ 0) (h_add : 1 + w.yf ≠ 0) :
    (mutateF w).y3 * (mutateF w).y4 = w.y3 * w.y4 * w.yf := by
  dsimp [mutateF]
  rw [inv_one_add_inv w.yf hyf h_add]
  have h_cancel : (1 + w.yf) * (w.yf * (1 + w.yf)⁻¹) = w.yf := by
    calc (1 + w.yf) * (w.yf * (1 + w.yf)⁻¹)
        = (1 + w.yf) * ((1 + w.yf)⁻¹ * w.yf) := by rw [mul_comm w.yf]
      _ = ((1 + w.yf) * (1 + w.yf)⁻¹) * w.yf := by rw [← mul_assoc]
      _ = 1 * w.yf := by rw [mul_inv_cancel₀ h_add]
      _ = w.yf := one_mul w.yf
  calc (w.y3 * (1 + w.yf)) * (w.y4 * (w.yf * (1 + w.yf)⁻¹))
      = (w.y3 * w.y4) * ((1 + w.yf) * (w.yf * (1 + w.yf)⁻¹)) := by ring
    _ = (w.y3 * w.y4) * w.yf := by rw [h_cancel]
    _ = w.y3 * w.y4 * w.yf := by rw [mul_assoc]

/-- Master Theorem 3 (Total Cluster Face Weight Monodromy Invariance):
    The overall 5-face product is strictly preserved under the square move:
    y_f' * (y₁' * y₂') * (y₃' * y₄') = y_f * (y₁ * y₂) * (y₃ * y₄). -/
theorem total_cluster_face_weight_monodromy (w : SquareFaceWeights F)
    (hyf : w.yf ≠ 0) (h_add : 1 + w.yf ≠ 0) :
    (mutateF w).yf * ((mutateF w).y1 * (mutateF w).y2) * ((mutateF w).y3 * (mutateF w).y4) =
    w.yf * (w.y1 * w.y2) * (w.y3 * w.y4) := by
  have h12 := square_move_opposite_pair_12 w hyf h_add
  have h34 := square_move_opposite_pair_34 w hyf h_add
  dsimp [mutateF] at h12 h34 ⊢
  rw [h12, h34]
  calc w.yf⁻¹ * (w.y1 * w.y2 * w.yf) * (w.y3 * w.y4 * w.yf)
      = (w.yf⁻¹ * w.yf) * (w.y1 * w.y2) * (w.y3 * w.y4 * w.yf) := by ring
    _ = 1 * (w.y1 * w.y2) * (w.y3 * w.y4 * w.yf) := by rw [inv_mul_cancel₀ hyf]
    _ = (w.y1 * w.y2) * (w.y3 * w.y4 * w.yf) := by rw [one_mul]
    _ = w.yf * (w.y1 * w.y2) * (w.y3 * w.y4) := by ring

/-- Master Theorem 4 (Cluster Mutation Involution):
    Mutating twice (reversing quiver arrows on the second mutation)
    recovers the exact initial cluster face weights:
    μ_f' ∘ μ_f = id. -/
theorem cluster_mutation_involution (w : SquareFaceWeights F)
    (hyf : w.yf ≠ 0) (h_add : 1 + w.yf ≠ 0) :
    mutateF_rev (mutateF w) = w := by
  have h_yf_inv_inv : (w.yf⁻¹)⁻¹ = w.yf := inv_inv w.yf
  have h_one_add_inv : 1 + w.yf⁻¹ ≠ 0 := one_add_inv_ne_zero w.yf hyf h_add
  have h_cancel_1 : (1 + w.yf) * (1 + (w.yf⁻¹)⁻¹)⁻¹ = 1 := by
    rw [h_yf_inv_inv]
    exact mul_inv_cancel₀ h_add
  have h_cancel_2 : (1 + w.yf⁻¹)⁻¹ * (1 + w.yf⁻¹) = 1 :=
    inv_mul_cancel₀ h_one_add_inv
  ext
  · exact h_yf_inv_inv
  · calc (mutateF_rev (mutateF w)).y1
        = w.y1 * (1 + w.yf) * (1 + (w.yf⁻¹)⁻¹)⁻¹ := rfl
      _ = w.y1 * ((1 + w.yf) * (1 + (w.yf⁻¹)⁻¹)⁻¹) := by rw [mul_assoc]
      _ = w.y1 * 1 := by rw [h_cancel_1]
      _ = w.y1 := mul_one w.y1
  · calc (mutateF_rev (mutateF w)).y2
        = w.y2 * (1 + w.yf⁻¹)⁻¹ * (1 + w.yf⁻¹) := rfl
      _ = w.y2 * ((1 + w.yf⁻¹)⁻¹ * (1 + w.yf⁻¹)) := by rw [mul_assoc]
      _ = w.y2 * 1 := by rw [h_cancel_2]
      _ = w.y2 := mul_one w.y2
  · calc (mutateF_rev (mutateF w)).y3
        = w.y3 * (1 + w.yf) * (1 + (w.yf⁻¹)⁻¹)⁻¹ := rfl
      _ = w.y3 * ((1 + w.yf) * (1 + (w.yf⁻¹)⁻¹)⁻¹) := by rw [mul_assoc]
      _ = w.y3 * 1 := by rw [h_cancel_1]
      _ = w.y3 := mul_one w.y3
  · calc (mutateF_rev (mutateF w)).y4
        = w.y4 * (1 + w.yf⁻¹)⁻¹ * (1 + w.yf⁻¹) := rfl
      _ = w.y4 * ((1 + w.yf⁻¹)⁻¹ * (1 + w.yf⁻¹)) := by rw [mul_assoc]
      _ = w.y4 * 1 := by rw [h_cancel_2]
      _ = w.y4 := mul_one w.y4

/-! ### 4. Compatibility with Cluster A-Variables (Ptolemy Relation) -/

/-- Master Theorem 5 (Ptolemy Compatibility):
    Let x_f * x_f' = x₁ x₃ + x₂ x₄ be the cluster A-exchange relation.
    Then the face weight monomial y_f = (x₁ x₃) / (x₂ x₄) satisfies:
    1 + y_f = (x_f * x_f') / (x₂ x₄). -/
theorem ptolemy_face_weight_add_one
    (xf xf' x1 x2 x3 x4 : F)
    (h_ptolemy : xf * xf' = x1 * x3 + x2 * x4)
    (h_denom : x2 * x4 ≠ 0) :
    1 + (x1 * x3) * (x2 * x4)⁻¹ = (xf * xf') * (x2 * x4)⁻¹ := by
  rw [h_ptolemy]
  calc 1 + (x1 * x3) * (x2 * x4)⁻¹
      = (x2 * x4) * (x2 * x4)⁻¹ + (x1 * x3) * (x2 * x4)⁻¹ := by
        rw [mul_inv_cancel₀ h_denom]
    _ = ((x2 * x4) + (x1 * x3)) * (x2 * x4)⁻¹ := by rw [add_mul]
    _ = (x1 * x3 + x2 * x4) * (x2 * x4)⁻¹ := by rw [add_comm]

/-- Master Theorem 6 (A-Variable Face Inversion):
    The inverted face weight y_f⁻¹ matches the dual monomial (x₂ x₄) / (x₁ x₃). -/
theorem ptolemy_face_weight_inv
    (x1 x2 x3 x4 : F)
    (_h13 : x1 * x3 ≠ 0) (_h24 : x2 * x4 ≠ 0) :
    ((x1 * x3) * (x2 * x4)⁻¹)⁻¹ = (x2 * x4) * (x1 * x3)⁻¹ := by
  calc ((x1 * x3) * (x2 * x4)⁻¹)⁻¹
      = (x2 * x4)⁻¹⁻¹ * (x1 * x3)⁻¹ := by rw [mul_inv_rev]
    _ = (x2 * x4) * (x1 * x3)⁻¹ := by rw [inv_inv]

end InfoGeometry.PlabicCluster
