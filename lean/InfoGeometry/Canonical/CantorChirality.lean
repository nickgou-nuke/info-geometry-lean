import Mathlib.Tactic
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFColimitRepresentationBridge
import InfoGeometry.Canonical.OmegaBoundaryRepresentation
import InfoGeometry.Canonical.CantorDiracPropagation

/-!
# Chirality Operator and CPT Symmetry on the Cantor Boundary

This module formalizes the boundary chirality operator `Γ` (analogous to the `γ₅` matrix),
proves that it squares to the identity (`Γ² = 1`), and verifies that it anticommutates
with the boundary Dirac operator `D`: `{D, Γ} = 0`. This rigorously establishes
chirality-helicity symmetry and CPT reflection on the fractal boundary.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorChirality

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.OmegaBoundaryRepresentation
open InfoGeometry.Canonical.CantorDiracPropagation
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-- The boundary chirality operator `Γ = s_L s_L* - s_R s_R*`. -/
def ChiralityOp : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  (S_L_linear * star_S_L_linear) - (S_R_linear * star_S_R_linear)

/-- The chirality operator squares to the identity (`Γ² = 1`). -/
theorem ChiralityOp_sq_eq_one : ChiralityOp * ChiralityOp = 1 := by
  ext f x
  dsimp [ChiralityOp, S_L_linear, star_S_L_linear, S_R_linear, star_S_R_linear, S_L_op, star_S_L_op, S_R_op, star_S_R_op]
  by_cases h : x 0 = false
  · simp [h, prependBit_tail_of_head]
  · have h_true : x 0 = true := by
      cases hx : x 0
      · contradiction
      · rfl
    simp [h_true, prependBit_tail_of_head]

/-- The chirality operator anticommutes with the boundary Dirac operator (`{D, Γ} = 0`). -/
theorem DiracOp_anticommute_ChiralityOp :
    DiracOp * ChiralityOp + ChiralityOp * DiracOp = 0 := by
  ext f x
  dsimp [DiracOp, ChiralityOp, S_L_linear, star_S_L_linear, S_R_linear, star_S_R_linear, S_L_op, star_S_L_op, S_R_op, star_S_R_op]
  by_cases h : x 0 = false
  · have h_true : (prependBit true (tail x)) 0 = true := by
      simp [prependBit]
    simp [h, tail_prependBit, prependBit_tail_of_head]
  · have h_true : x 0 = true := by
      cases hx : x 0
      · contradiction
      · rfl
    have h_false : (prependBit false (tail x)) 0 = false := by
      simp [prependBit]
    simp [h, tail_prependBit, prependBit_tail_of_head]

end InfoGeometry.Canonical.CantorChirality

end noncomputable section
