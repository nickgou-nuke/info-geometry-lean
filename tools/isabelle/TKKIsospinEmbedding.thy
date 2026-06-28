theory TKKIsospinEmbedding
  imports Main
begin

text ‹
  TKK (Tits-Kantor-Koecher) Isospin Embedding
  Formalizes a TKK algebra with 5 gradings and an embedded SU(2) sub-algebra
  in the zero grading.
›

locale tkk_algebra =
  fixes G_minus_2 :: "'a set"
    and G_minus_1 :: "'a set"
    and G_zero :: "'a set"
    and G_plus_1 :: "'a set"
    and G_plus_2 :: "'a set"
    and bracket :: "'a ⇒ 'a ⇒ 'a"
  assumes
    bracket_m2_p2: "⟦ x ∈ G_minus_2; y ∈ G_plus_2 ⟧ ⟹ bracket x y ∈ G_zero"
    and bracket_m1_p1: "⟦ x ∈ G_minus_1; y ∈ G_plus_1 ⟧ ⟹ bracket x y ∈ G_zero"
    and bracket_0_0: "⟦ x ∈ G_zero; y ∈ G_zero ⟧ ⟹ bracket x y ∈ G_zero"

locale su2_subalgebra = tkk_algebra +
  fixes J_plus :: "'a"
    and J_minus :: "'a"
    and J_z :: "'a"
  assumes
    J_plus_in_G_zero: "J_plus ∈ G_zero"
    and J_minus_in_G_zero: "J_minus ∈ G_zero"
    and J_z_in_G_zero: "J_z ∈ G_zero"
    and J_z_J_plus: "bracket J_z J_plus = J_plus"
    and J_z_J_minus: "bracket J_z J_minus = J_minus"
    and J_plus_J_minus: "bracket J_plus J_minus = J_z"

context su2_subalgebra
begin

lemma triality_symmetry_breaking:
  assumes non_commutative: "bracket J_plus J_minus ≠ bracket J_minus J_plus"
  shows "bracket J_plus J_minus ≠ bracket J_minus J_z"
  sorry

end

end
