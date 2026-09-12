import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.LocallyConvex.Separation
import InfoGeometry.Convex.FenchelConjugate

namespace InfoGeometry.Convex

noncomputable section

def extendedFenchelSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : DualSpace E) : Set EReal :=
  Set.range (fun x : E => (y x : EReal) - f x)

def extendedFenchelConj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : DualSpace E) : EReal :=
  sSup (extendedFenchelSet f y)

def extendedFenchelBiconj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x : E) : EReal :=
  sSup (Set.range (fun y : DualSpace E => (y x : EReal) - extendedFenchelConj f y))

theorem extendedFenchelConj_le_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : DualSpace E) (a : EReal) :
    extendedFenchelConj f y ≤ a ↔
      ∀ x : E, (y x : EReal) - f x ≤ a := by
  constructor
  · intro h x
    exact le_trans (le_sSup (s := extendedFenchelSet f y) ⟨x, rfl⟩) h
  · intro h
    apply sSup_le
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact h x

structure IsProperEReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : Prop where
  neverBot : ∀ x, f x ≠ ⊥
  finitePoint : ∃ x, f x ≠ ⊤

def epigraph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

def IsConvexEReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : Prop := Convex ℝ (epigraph f)

def IsLowerSemicontinuousEReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → EReal) : Prop := IsClosed (epigraph f)

theorem epigraph_separates_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x : E) (r : ℝ)
    (hconv : IsConvexEReal f) (hclosed : IsLowerSemicontinuousEReal f)
    (hout : (x, r) ∉ epigraph f) :
    ∃ ℓ : StrongDual ℝ (E × ℝ), ∃ u : ℝ,
      (∀ p ∈ epigraph f, ℓ p < u) ∧ u < ℓ (x, r) := by
  exact geometric_hahn_banach_closed_point hconv hclosed hout

def separatorPrimalValue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : StrongDual ℝ (E × ℝ)) (x : E) : ℝ := ℓ (x, 0)

def separatorVerticalValue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : StrongDual ℝ (E × ℝ)) : ℝ := ℓ (0, 1)

theorem separator_value_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : StrongDual ℝ (E × ℝ)) (x : E) (r : ℝ) :
    ℓ (x, r) = separatorPrimalValue ℓ x + r * separatorVerticalValue ℓ := by
  rw [show (x, r) = (x, 0) + r • (0, 1) by ext <;> simp]
  rw [map_add, map_smul]
  rfl

structure ProperConvexEReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : Prop where
  proper : IsProperEReal f
  convex : IsConvexEReal f

structure ProperConvexLowerSemicontinuousEReal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal) : Prop where
  proper : IsProperEReal f
  convex : IsConvexEReal f
  lowerSemicontinuous : IsLowerSemicontinuousEReal f

def FiniteOnEReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : Prop := ∃ value : E → ℝ, ∀ x, f x = (value x : EReal)

theorem epigraph_mem_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x : E) (r : ℝ) :
    (x, r) ∈ epigraph f ↔ f x ≤ (r : EReal) := by
  rfl

theorem epigraph_not_mem_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x : E) (r : ℝ) :
    (x, r) ∉ epigraph f ↔ (r : EReal) < f x := by
  rw [epigraph_mem_iff]
  exact not_le

theorem extendedFenchelConj_ne_bot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : DualSpace E) (x : E)
    (hf_bot : f x ≠ ⊥) (hf_top : f x ≠ ⊤) :
    extendedFenchelConj f y ≠ ⊥ := by
  intro hbot
  have hmem : (y x : EReal) - f x ∈ extendedFenchelSet f y := ⟨x, rfl⟩
  have hle := le_sSup hmem
  change sSup (extendedFenchelSet f y) = ⊥ at hbot
  rw [hbot] at hle
  exact (not_le_of_gt (EReal.bot_lt_coe (y x)) )
    ((EReal.sub_le_iff_le_add (Or.inl hf_bot) (Or.inl hf_top)).mp hle)

theorem proper_extendedFenchelConj_ne_bot
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : DualSpace E) (hf : IsProperEReal f) :
    extendedFenchelConj f y ≠ ⊥ := by
  rcases hf.finitePoint with ⟨x, hx⟩
  exact extendedFenchelConj_ne_bot f y x (hf.neverBot x) hx

theorem extendedFenchelConj_ne_top_of_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : DualSpace E) (b : ℝ)
    (hbound : ∀ x : E, (y x : EReal) - f x ≤ (b : EReal)) :
    extendedFenchelConj f y ≠ ⊤ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (sSup_le (by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact hbound x))
  exact EReal.coe_lt_top b

theorem extendedFenchelSet_nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : DualSpace E) :
    (extendedFenchelSet f y).Nonempty := by
  exact ⟨(y 0 : EReal) - f 0, ⟨0, rfl⟩⟩

theorem extendedFenchelYoung {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (y : DualSpace E) (x : E)
    (hf_bot : f x ≠ ⊥) (hf_top : f x ≠ ⊤) :
    (y x : EReal) ≤ f x + extendedFenchelConj f y := by
  have h := le_sSup (s := extendedFenchelSet f y)
    (⟨x, rfl⟩ : (y x : EReal) - f x ∈ extendedFenchelSet f y)
  change (y x : EReal) - f x ≤ extendedFenchelConj f y at h
  have h' := (EReal.sub_le_iff_le_add (Or.inl hf_bot) (Or.inl hf_top)).mp h
  simpa [add_comm] using h'

theorem extendedFenchelBiconj_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x : E) (hbot : f x ≠ ⊥) (htop : f x ≠ ⊤) :
    extendedFenchelBiconj f x ≤ f x := by
  unfold extendedFenchelBiconj
  apply sSup_le
  intro z hz
  rcases hz with ⟨y, rfl⟩
  by_cases hc : extendedFenchelConj f y = ⊤
  · simp [hc]
  · exact (EReal.sub_le_iff_le_add
      (Or.inl (extendedFenchelConj_ne_bot f y x hbot htop)) (Or.inl hc)).mpr
      (extendedFenchelYoung f y x hbot htop)

theorem le_extendedFenchelBiconj_of_dual_witness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x : E) (t : EReal)
    (h : ∃ y : DualSpace E, t ≤ (y x : EReal) - extendedFenchelConj f y) :
    t ≤ extendedFenchelBiconj f x := by
  rcases h with ⟨y, hy⟩
  exact hy.trans (le_sSup (s := Set.range (fun z : DualSpace E =>
    (z x : EReal) - extendedFenchelConj f z)) ⟨y, rfl⟩)

theorem extendedFenchel_le_biconj_of_all_lower_witnesses
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x : E)
    (h : ∀ t : EReal, t < f x → t ≤ extendedFenchelBiconj f x) :
    f x ≤ extendedFenchelBiconj f x := by
  exact le_of_forall_lt_imp_le_of_dense h

theorem epigraph_separates_strictly_below
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x : E) (r : ℝ)
    (hconv : IsConvexEReal f) (hclosed : IsLowerSemicontinuousEReal f)
    (hr : (r : EReal) < f x) :
    ∃ ℓ : StrongDual ℝ (E × ℝ), ∃ u : ℝ,
      (∀ p ∈ epigraph f, ℓ p < u) ∧ u < ℓ (x, r) := by
  apply epigraph_separates_point f x r hconv hclosed
  exact epigraph_not_mem_iff f x r |>.mpr hr

end
end InfoGeometry.Convex
