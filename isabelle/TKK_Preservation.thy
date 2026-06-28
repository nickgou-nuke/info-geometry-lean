theory TKK_Preservation
  imports Main
begin

section ‹Tits-Kantor-Koecher (TKK) 5-Grading›

text ‹
  This theory formalizes the 5-graded structure of the Tits-Kantor-Koecher (TKK) algebra.
  The TKK algebra is a Lie algebra constructed from a Jordan algebra (or Jordan triple system),
  and it decomposes into five graded components: L_{-2}, L_{-1}, L_0, L_1, L_2.
›

locale tkk_algebra =
  fixes L :: "int ⇒ 'a set"
  fixes zero :: "'a" ("𝟬")
  fixes bracket :: "'a ⇒ 'a ⇒ 'a" (infixl "⋆" 70)
  assumes L_empty_out_of_bounds: "i < -2 ∨ i > 2 ⟹ L i = {𝟬}"
  assumes bracket_grading: "x ∈ L i ⟹ y ∈ L j ⟹ (x ⋆ y) ∈ L (i + j)"
begin

definition L_m2 :: "'a set" where "L_m2 = L (-2)"
definition L_m1 :: "'a set" where "L_m1 = L (-1)"
definition L_0  :: "'a set" where "L_0 = L 0"
definition L_p1 :: "'a set" where "L_p1 = L 1"
definition L_p2 :: "'a set" where "L_p2 = L 2"

theorem grading_preservation:
  assumes "x ∈ L i" and "y ∈ L j"
  shows "(x ⋆ y) ∈ L (i + j)"
  using assms bracket_grading by simp

lemma bracket_L_m2_L_p2:
  assumes "x ∈ L_m2" and "y ∈ L_p2"
  shows "(x ⋆ y) ∈ L_0"
proof -
  have "x ∈ L (-2)" using assms L_m2_def by simp
  moreover have "y ∈ L 2" using assms L_p2_def by simp
  ultimately have "(x ⋆ y) ∈ L (-2 + 2)" using bracket_grading by blast
  then show ?thesis using L_0_def by simp
qed

lemma bracket_L_p1_L_p1:
  assumes "x ∈ L_p1" and "y ∈ L_p1"
  shows "(x ⋆ y) ∈ L_p2"
proof -
  have "x ∈ L 1" using assms L_p1_def by simp
  moreover have "y ∈ L 1" using assms L_p1_def by simp
  ultimately have "(x ⋆ y) ∈ L (1 + 1)" using bracket_grading by blast
  then show ?thesis using L_p2_def by simp
qed

lemma bracket_L_p1_L_p2:
  assumes "x ∈ L_p1" and "y ∈ L_p2"
  shows "(x ⋆ y) = 𝟬"
proof -
  have "x ∈ L 1" using assms L_p1_def by simp
  moreover have "y ∈ L 2" using assms L_p2_def by simp
  ultimately have "(x ⋆ y) ∈ L (1 + 2)" using bracket_grading by blast
  hence "(x ⋆ y) ∈ L 3" by simp
  moreover have "L 3 = {𝟬}" using L_empty_out_of_bounds by simp
  ultimately show ?thesis by simp
qed

end

end
