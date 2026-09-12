import Mathlib.Analysis.LocallyConvex.Separation

namespace InfoGeometry.EpigraphHahnBanachSeparation


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyConvexSpace ℝ E]

def epigraph (f : E → ℝ) : Set (E × ℝ) := {p | f p.1 ≤ p.2}

theorem convex_epigraph {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    Convex ℝ (epigraph f) := by
  intro p hp q hq a b ha hb hab
  change f p.1 ≤ p.2 at hp
  change f q.1 ≤ q.2 at hq
  change f (a • p.1 + b • q.1) ≤ a * p.2 + b * q.2
  have h := hf.2 (x := p.1) (y := q.1) (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hp' : a * f p.1 ≤ a * p.2 := mul_le_mul_of_nonneg_left hp ha
  have hq' : b * f q.1 ≤ b * q.2 := mul_le_mul_of_nonneg_left hq hb
  simpa [smul_eq_mul] using h.trans (add_le_add hp' hq')

theorem strict_separation {f : E → ℝ}
    (hconv : Convex ℝ (epigraph f)) (hclosed : IsClosed (epigraph f))
    (x : E) (t : ℝ) (hout : t < f x) :
    ∃ L : StrongDual ℝ (E × ℝ), ∃ c : ℝ,
      (∀ p ∈ epigraph f, L p < c) ∧ c < L (x, t) := by
  have hnot : (x, t) ∉ epigraph f := by
    intro h
    exact (not_le_of_gt hout) h
  rcases geometric_hahn_banach_closed_point hconv hclosed hnot with ⟨L, c, hL, hc⟩
  exact ⟨L, c, hL, hc⟩

structure AffineMinorant (f : E → ℝ) where
  slope : E →L[ℝ] ℝ
  intercept : ℝ
  is_minorant : ∀ x, slope x + intercept ≤ f x

theorem affine_minorant_coe {f : E → ℝ} (M : AffineMinorant f) (x : E) :
    ((M.slope x + M.intercept : ℝ) : EReal) ≤ (f x : EReal) := by
  exact_mod_cast M.is_minorant x

theorem extract_affine_minorant {f : E → ℝ}
    (L : StrongDual ℝ (E × ℝ)) (c : ℝ) (x₀ : E) (t₀ : ℝ)
    (hbelow : ∀ p ∈ epigraph f, L p < c) (habove : c < L (x₀,t₀))
    (hα : L (0,1) < 0) :
    ∃ M : AffineMinorant f, M.slope x₀ + M.intercept > t₀ := by
  let α : ℝ := - L (0,1)
  have hαpos : 0 < α := by dsimp [α]; linarith
  let xstar : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ E) (0 : E →L[ℝ] ℝ))
  have hdecomp (x : E) (t : ℝ) : L (x,t) = xstar x - α*t := by
    have hs : (x,t) = (x,0) + t • (0,1) := by ext <;> simp
    rw [hs, map_add, map_smul]
    dsimp [xstar, α]
    ring
  let m : E →L[ℝ] ℝ := (α⁻¹) • xstar
  let b : ℝ := -(c * α⁻¹)
  have hm : ∀ x, m x + b ≤ f x := by
    intro x
    have hmem : (x, f x) ∈ epigraph f := by
      change f x ≤ f x
      exact le_rfl
    have h := hbelow (x, f x) hmem
    rw [hdecomp] at h
    have hi : (0:ℝ) < α⁻¹ := inv_pos.mpr hαpos
    have := (mul_lt_mul_of_pos_right h hi)
    dsimp [m,b]
    have ha : α * α⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hαpos)
    field_simp [ha] at this ⊢
    linarith
  have htarget : m x₀ + b > t₀ := by
    have h := habove
    rw [hdecomp] at h
    have hi : (0:ℝ) < α⁻¹ := inv_pos.mpr hαpos
    have := (mul_lt_mul_of_pos_right h hi)
    dsimp [m,b]
    have ha : α * α⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hαpos)
    field_simp [ha] at this ⊢
    linarith
  exact ⟨⟨m,b,hm⟩, htarget⟩

theorem fenchel_moreau_topological_bridge {f : E → ℝ}
    (hconv : Convex ℝ (epigraph f)) (hclosed : IsClosed (epigraph f))
    (x₀ : E) (t₀ : ℝ) (hout : t₀ < f x₀) :
    ∃ M : AffineMinorant f, M.slope x₀ + M.intercept > t₀ := by
  rcases strict_separation hconv hclosed x₀ t₀ hout with ⟨L,c,hbelow,habove⟩
  have hv : L (0,1) < 0 := by
    have hm : (x₀, f x₀) ∈ epigraph f := by
      change f x₀ ≤ f x₀
      exact le_rfl
    have h1 := hbelow (x₀, f x₀) hm
    have hd : L (x₀, f x₀) - L (x₀,t₀) < 0 := sub_neg.mpr (lt_trans h1 habove)
    rw [← map_sub] at hd
    have heq : (x₀, f x₀) - (x₀,t₀) = (f x₀ - t₀) • (0,1) := by ext <;> simp
    rw [heq, map_smul] at hd
    have hp : 0 < f x₀ - t₀ := sub_pos.mpr hout
    have hd' : (f x₀ - t₀) * L (0,1) < 0 := by simpa [smul_eq_mul] using hd
    nlinarith
  exact extract_affine_minorant L c x₀ t₀ hbelow habove hv


end InfoGeometry.EpigraphHahnBanachSeparation
