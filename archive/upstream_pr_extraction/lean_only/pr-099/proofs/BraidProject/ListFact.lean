import Mathlib.Data.List.Basic

theorem list_splits_somewhere {a b c d : List α} (h : a ++ b = c ++ d) :
    a = c ∨ (∃ to_middle, a = c ++ to_middle ∧ d = to_middle ++ b) ∨
    (∃ from_middle, a ++ from_middle = c ∧ b = from_middle ++ d) := by
  rcases (List.append_eq_append_iff.mp h) with ⟨from_middle, hc, hb⟩ | ⟨to_middle, ha, hd⟩
  · exact Or.inr (Or.inr ⟨from_middle, hc.symm, hb⟩)
  · exact Or.inr (Or.inl ⟨to_middle, ha, hd⟩)
