theory ProjectiveStateSpace
  imports Main
begin

typedef 'a projective_ray = "{S :: 'a set. S ≠ {}}"
  by blast

definition equivalence_class :: "'a set ⇒ 'a set ⇒ bool" where
  "equivalence_class A B ⟷ (A = B)"

lemma topological_continuity_stub: "True"
  by simp

end
