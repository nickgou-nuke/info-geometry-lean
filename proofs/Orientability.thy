theory Orientability
  imports Main Real
begin

text ‹Formulate the foundational topological definition of orientable covers.›

record 'a Cover = 
  patches :: "'a set set"
  is_cover :: "Union patches = UNIV"

definition orientable_cover :: "'a Cover ⇒ bool" where
  "orientable_cover C ⟷ (∃ orientation_map. ∀ P ∈ patches C. ∀ Q ∈ patches C. 
     P ∩ Q ≠ {} ⟶ orientation_map P Q > (0::real))"

lemma orientable_implies_positive:
  assumes "orientable_cover C"
  shows "∃ orientation_map. ∀ P ∈ patches C. ∀ Q ∈ patches C. 
         P ∩ Q ≠ {} ⟶ orientation_map P Q > (0::real)"
  using assms unfolding orientable_cover_def by auto

end
