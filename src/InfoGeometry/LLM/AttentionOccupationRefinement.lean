/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LLM.AttentionFrameCorrections
import InfoGeometry.Optics.SheetWittCircularBasis

/-!
# Joint spectral refinement of overlapping occupations

Contract: keep the actual operators on `BitSpace` from the attention-frame
owner. Their bit parities instantiate the existing `CommutingInvolutions`
construction. The four joint sectors are pairwise disjoint idempotents summing
to one; each original occupation is a marginal sum. This resolves overlap by
refinement, without falsely declaring either original projector central or
identifying independent tensor occupations with direct-product heads.
-/

noncomputable section

namespace InfoGeometry.LLM.AttentionOccupationRefinement

open AttentionFrameCorrections
open InfoGeometry.Optics.SheetWittCircularBasis

theorem bitParity_square (k : Fin 2) : bitParity k * bitParity k = 1 := by
  ext x b
  by_cases hb : b k = false <;> simp [bitParity, Module.End.mul_apply, hb]

theorem bitParity_commute (k l : Fin 2) :
    bitParity k * bitParity l = bitParity l * bitParity k := by
  ext x b
  by_cases hk : b k = false <;> by_cases hl : b l = false <;>
    simp [bitParity, Module.End.mul_apply, hk, hl]

/-- Source-defined parity axes, certified for the existing joint spectrum API. -/
def occupationAxes : CommutingInvolutions (Module.End ℝ BitSpace) where
  hyperbolic := bitParity 0
  circular := bitParity 1
  hyperbolic_sq := bitParity_square 0
  circular_sq := bitParity_square 1
  commute := bitParity_commute 0 1
  projector_commute := by
    intro ε σ
    ext x b
    cases ε <;> cases σ <;>
      by_cases h0 : b 0 = false <;> by_cases h1 : b 1 = false <;>
      simp [choose, bitParity, Module.End.mul_apply, h0, h1] <;> ring

/-- The joint true/true sector is exactly the previously observed overlap. -/
theorem joint_true_true_eq_overlap :
    occupationAxes.jointProjector true true = occupationProjection 0 * occupationProjection 1 := by
  rw [occupationProjection_eq, occupationProjection_eq]
  rfl

/-- Each joint sector is an idempotent in the full endomorphism algebra. -/
theorem joint_sector_idempotent (ε σ : Bool) :
    occupationAxes.jointProjector ε σ * occupationAxes.jointProjector ε σ =
      occupationAxes.jointProjector ε σ := occupationAxes.jointProjector_idem ε σ

/-- Distinct joint labels have disjoint operator ranges. -/
theorem joint_sectors_disjoint (ε σ ε' σ' : Bool) (h : ε ≠ ε' ∨ σ ≠ σ') :
    occupationAxes.jointProjector ε σ * occupationAxes.jointProjector ε' σ' = 0 :=
  occupationAxes.jointProjectors_pairwise_disjoint ε σ ε' σ' h

/-- The complete identity resolution uses all four joint sectors. -/
theorem joint_sectors_complete :
    occupationAxes.jointProjector true true + occupationAxes.jointProjector true false +
      occupationAxes.jointProjector false true + occupationAxes.jointProjector false false = 1 :=
  occupationAxes.jointProjector_sum

/-- The first occupation is the marginal over the second parity. -/
theorem first_occupation_marginal :
    occupationAxes.jointProjector true true + occupationAxes.jointProjector true false =
      occupationProjection 0 := by
  rw [occupationAxes.jointProjector_sum_circular, occupationProjection_eq]
  rfl

/-- The second occupation is the marginal over the first parity. -/
theorem second_occupation_marginal :
    occupationAxes.jointProjector true true + occupationAxes.jointProjector false true =
      occupationProjection 1 := by
  rw [occupationAxes.jointProjector_sum_hyperbolic, occupationProjection_eq]
  rfl

end InfoGeometry.LLM.AttentionOccupationRefinement
