import Mathlib
import InfoGeometry.Analysis.L2CantorCommutation

open InfoGeometry.Analysis.L2CantorCommutation

/-!
# Jaynes Relative States — Cuntz branch weights

This module keeps the Jaynes/Cuntz `1 / 2` branch-weight derivation on the
concrete `L2CantorCommutation` operator lane.

The generic owner algebraic theorem is in
`InfoGeometry.Analysis.AxiomFreeGNS.branch_weight_one_half`. This file records
the same transparent calculation on the concrete Cuntz range projections.

No global postulate declarations are introduced here.

#### BUCKET 1: CLOSED FINITE THEOREMS
`branch_weight_one_half_on_cuntz_projections` is closed by instantiating the
generic additive-functional theorem with the proved concrete Cuntz partition.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The concrete theorem depends only on normalization and left-right symmetry of
the caller's additive functional.

#### BUCKET 3: OPEN CLOSURE DEBT
None for this branch-weight readback.
-/

namespace InfoGeometry.Analysis.JaynesRelativeStates

/-- Additive-hom specialization to the concrete Cuntz range projections. -/
theorem branch_weight_one_half_on_cuntz_projections
    (φ : (H → H) →+ ℝ)
    (h_one : φ id = 1)
    (h_symm : φ (S_left ∘ star_S_left) = φ (S_right ∘ star_S_right)) :
    φ (S_left ∘ star_S_left) = (1 / 2 : ℝ) ∧
    φ (S_right ∘ star_S_right) = (1 / 2 : ℝ) := by
  have h_sum :
      φ (S_left ∘ star_S_left) + φ (S_right ∘ star_S_right) = (1 : ℝ) := by
    calc
      φ (S_left ∘ star_S_left) + φ (S_right ∘ star_S_right)
          = φ ((S_left ∘ star_S_left) + (S_right ∘ star_S_right)) := by
            exact (φ.map_add (S_left ∘ star_S_left) (S_right ∘ star_S_right)).symm
      _ = φ id := by rw [S_left_star_S_left_add_S_right_star_S_right]
      _ = 1 := h_one
  have h_double : (2 : ℝ) * φ (S_left ∘ star_S_left) = 1 := by
    calc
      (2 : ℝ) * φ (S_left ∘ star_S_left)
          = φ (S_left ∘ star_S_left) + φ (S_left ∘ star_S_left) := by ring
      _ = φ (S_left ∘ star_S_left) + φ (S_right ∘ star_S_right) := by
        rw [h_symm]
      _ = 1 := h_sum
  have h_left : φ (S_left ∘ star_S_left) = (1 / 2 : ℝ) := by
    calc
      φ (S_left ∘ star_S_left)
          = ((2 : ℝ) * φ (S_left ∘ star_S_left)) * (1 / 2 : ℝ) := by ring
      _ = 1 * (1 / 2 : ℝ) := by rw [h_double]
      _ = (1 / 2 : ℝ) := by ring
  exact ⟨h_left, by rw [← h_symm, h_left]⟩

end InfoGeometry.Analysis.JaynesRelativeStates
