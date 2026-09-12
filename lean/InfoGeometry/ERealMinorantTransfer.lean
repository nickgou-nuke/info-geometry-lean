import Mathlib.Data.EReal.Operations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import InfoGeometry.Convex.ExtendedFenchel
import InfoGeometry.EpigraphHahnBanachSeparation

/-! A pointwise affine minorant transfer over the extended reals. -/

theorem ereal_minorant_transfer_point
    (y_z : ℝ) (b : ℝ) (fE_z : EReal)
    (h_bound : (y_z : EReal) + (b : EReal) ≤ fE_z) :
    (y_z : EReal) - fE_z ≤ -(b : EReal) := by
  have h_cases : fE_z = ⊥ ∨ (∃ r : ℝ, fE_z = (r : EReal)) ∨ fE_z = ⊤ := by
    cases fE_z with
    | bot => exact Or.inl rfl
    | coe r => exact Or.inr (Or.inl ⟨r, rfl⟩)
    | top => exact Or.inr (Or.inr rfl)
  rcases h_cases with h_bot | ⟨r, h_real⟩ | h_top
  · rw [h_bot] at h_bound
    exact False.elim ((not_le_of_gt (EReal.bot_lt_coe (y_z + b))) h_bound)
  · rw [h_real] at h_bound ⊢
    have h_bound_real : y_z + b ≤ r := by exact_mod_cast h_bound
    have h_goal_real : y_z - r ≤ -b := by linarith
    exact_mod_cast h_goal_real
  · rw [h_top]
    exact bot_le

namespace InfoGeometry.ERealMinorantTransfer

open InfoGeometry.Convex
open InfoGeometry.EpigraphHahnBanachSeparation

/-- An affine minorant gives a finite upper bound for the extended Fenchel
conjugate of a real-valued function. -/
theorem affine_minorant_extendedFenchelConj_ne_top
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (M : AffineMinorant f) :
    extendedFenchelConj (fun x : E => (f x : EReal)) M.slope ≠ ⊤ := by
  apply extendedFenchelConj_ne_top_of_bound
  intro x
  have hminorant :
      ((M.slope x + M.intercept : ℝ) : EReal) ≤ (f x : EReal) :=
    affine_minorant_coe M x
  have htransfer :=
    ereal_minorant_transfer_point (M.slope x) M.intercept (f x) hminorant
  simpa using htransfer

/-- An affine minorant supplies the lower witness required by the extended
Fenchel biconjugate. -/
theorem lower_bound_from_affine_minorant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (M : AffineMinorant f) (x : E) (t : ℝ)
    (ht : t ≤ M.slope x + M.intercept) :
    (t : EReal) ≤ extendedFenchelBiconj
      (fun z : E => (f z : EReal)) x := by
  let F : E → EReal := fun z => (f z : EReal)
  have hconj : extendedFenchelConj F M.slope ≤ -(M.intercept : EReal) := by
    apply (extendedFenchelConj_le_iff F M.slope _).mpr
    intro z
    have hminorant :
        ((M.slope z + M.intercept : ℝ) : EReal) ≤ (f z : EReal) :=
      affine_minorant_coe M z
    simpa [F] using
      (ereal_minorant_transfer_point (M.slope z) M.intercept (f z) hminorant)
  have ht' : (t : EReal) ≤ (M.slope x : EReal) + (M.intercept : EReal) := by
    exact_mod_cast ht
  have hsum :
      (t : EReal) + extendedFenchelConj F M.slope ≤ (M.slope x : EReal) := by
    calc
      (t : EReal) + extendedFenchelConj F M.slope ≤
          ((M.slope x : ℝ) + M.intercept : EReal) +
            extendedFenchelConj F M.slope := by
              simpa [add_assoc, add_left_comm, add_comm] using
                add_le_add_right ht' (extendedFenchelConj F M.slope)
      _ ≤ (M.slope x : EReal) := by
        calc
          ((M.slope x : ℝ) + M.intercept : EReal) +
              extendedFenchelConj F M.slope ≤
              ((M.slope x : ℝ) + M.intercept : EReal) +
                (-(M.intercept : EReal)) := add_le_add_right hconj _
          _ = (M.slope x : EReal) := by
            change ((M.slope x + M.intercept - M.intercept : ℝ) : EReal) = _
            rw [add_sub_cancel_right]
  have hwitness :
      (t : EReal) ≤ (M.slope x : EReal) - extendedFenchelConj F M.slope := by
    have htop : extendedFenchelConj F M.slope ≠ ⊤ := by
      simpa [F] using affine_minorant_extendedFenchelConj_ne_top f M
    exact (EReal.le_sub_iff_add_le
      (Or.inl (extendedFenchelConj_ne_bot F M.slope x (by simp [F]) (by simp [F])))
      (Or.inl htop)).mpr hsum
  simpa [F] using
    (le_extendedFenchelBiconj_of_dual_witness F x t ⟨M.slope, hwitness⟩)

/-- A closed convex real epigraph yields the lower half of the extended
Fenchel--Moreau inequality. -/
theorem coe_le_extendedFenchelBiconj
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ)
    (hconv : Convex ℝ (epigraph f))
    (hclosed : IsClosed (epigraph f)) :
    ∀ x : E,
      (f x : EReal) ≤
        extendedFenchelBiconj (fun z : E => (f z : EReal)) x := by
  intro x
  apply extendedFenchel_le_biconj_of_all_lower_witnesses
    (fun z : E => (f z : EReal)) x
  intro t ht
  cases t with
  | bot => exact bot_le
  | coe t =>
      have ht_real : t < f x := by exact_mod_cast ht
      rcases fenchel_moreau_topological_bridge hconv hclosed x t ht_real with ⟨M, hM⟩
      exact lower_bound_from_affine_minorant f M x t (le_of_lt hM)
  | top => exact (not_lt_of_ge (le_top) ht).elim

end InfoGeometry.ERealMinorantTransfer
