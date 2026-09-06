module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.LinearAlgebra.JordanChevalley

/-! Project-owned compatibility theorem for the pinned Jordan--Chevalley API. -/

public section

open Algebra Polynomial

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

public theorem isNilpotent_isSemisimple_unique [PerfectField K]
    {n₁ s₁ n₂ s₂ : End K V}
    (hn₁ : IsNilpotent n₁) (hs₁ : s₁.IsSemisimple)
    (hn₂ : IsNilpotent n₂) (hs₂ : s₂.IsSemisimple)
    (hc₁ : Commute n₁ s₁) (hc₂ : Commute n₂ s₂)
    (h : n₁ + s₁ = n₂ + s₂) :
    n₁ = n₂ ∧ s₁ = s₂ := by
  obtain ⟨n₀, hn₀, s₀, hs₀, hn₀_nil, hs₀_ss, h₀⟩ :=
    (n₁ + s₁).exists_isNilpotent_isSemisimple
  suffices ∀ {n s}, IsNilpotent n → s.IsSemisimple → Commute n s →
      n₁ + s₁ = n + s → s = s₀ by grind
  intro n s hn hs hc heq
  have hsf : Commute s (n₁ + s₁) := heq ▸ hc.symm.add_right (Commute.refl s)
  have hnf : Commute n (n₁ + s₁) := heq ▸ (Commute.refl n).add_right hc
  have hnil : IsNilpotent (s - s₀) := by
    rw [show s - s₀ = n₀ - n from by grind]
    exact (commute_of_mem_adjoin_singleton_of_commute hn₀ hnf).symm.isNilpotent_sub hn₀_nil hn
  have hss : (s - s₀).IsSemisimple :=
    hs.sub_of_commute (commute_of_mem_adjoin_singleton_of_commute hs₀ hsf) hs₀_ss
  grind [eq_zero_of_isNilpotent_isSemisimple hnil hss]

end Module.End
