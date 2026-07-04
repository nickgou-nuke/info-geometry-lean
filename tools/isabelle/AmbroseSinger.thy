theory AmbroseSinger
  imports Main
begin

text \<open>Abstract Formalization of Ambrose-Singer Holonomy Reduction\<close>

typedecl point
typedecl vector
typedecl algebra_element

consts
  Curvature :: "point \<Rightarrow> vector \<Rightarrow> vector \<Rightarrow> algebra_element"
  HolonomyAlgebra :: "point \<Rightarrow> algebra_element set"
  HorizontalVectors :: "point \<Rightarrow> vector set"
  algebra_span :: "algebra_element set \<Rightarrow> algebra_element set"

axiomatization where
  span_inc: "x \<in> S \<Longrightarrow> x \<in> algebra_span S" and
  span_mono: "S \<subseteq> T \<Longrightarrow> algebra_span S \<subseteq> algebra_span T" and
  span_idempotent: "algebra_span (algebra_span S) = algebra_span S"

axiomatization where
  ambrose_singer: "HolonomyAlgebra p = algebra_span {Curvature p X Y | X Y. X \<in> HorizontalVectors p \<and> Y \<in> HorizontalVectors p}"

lemma curvature_in_holonomy:
  assumes "X \<in> HorizontalVectors p" "Y \<in> HorizontalVectors p"
  shows "Curvature p X Y \<in> HolonomyAlgebra p"
proof -
  have "Curvature p X Y \<in> {Curvature p X Y | X Y. X \<in> HorizontalVectors p \<and> Y \<in> HorizontalVectors p}"
    using assms by blast
  then show ?thesis
    using ambrose_singer[of p] span_inc by auto
qed

lemma holonomy_reduction_map:
  assumes "HorizontalVectors p \<noteq> {}"
  assumes "\<forall>X \<in> HorizontalVectors p. \<forall>Y \<in> HorizontalVectors p. Curvature p X Y = c"
  shows "HolonomyAlgebra p = algebra_span {c}"
proof -
  from assms(1) obtain X where "X \<in> HorizontalVectors p" by blast
  have "{Curvature p X Y | X Y. X \<in> HorizontalVectors p \<and> Y \<in> HorizontalVectors p} = {c}"
  proof (rule set_eqI)
    fix x
    show "(x \<in> {Curvature p X Y | X Y. X \<in> HorizontalVectors p \<and> Y \<in> HorizontalVectors p}) = (x \<in> {c})"
    proof
      assume "x \<in> {Curvature p X Y | X Y. X \<in> HorizontalVectors p \<and> Y \<in> HorizontalVectors p}"
      then obtain A B where "x = Curvature p A B" "A \<in> HorizontalVectors p" "B \<in> HorizontalVectors p" by auto
      then have "x = c" using assms(2) by simp
      then show "x \<in> {c}" by simp
    next
      assume "x \<in> {c}"
      then have "x = c" by simp
      have "c = Curvature p X X" using `X \<in> HorizontalVectors p` assms(2) by simp
      then have "x = Curvature p X X" using `x = c` by simp
      then show "x \<in> {Curvature p X Y | X Y. X \<in> HorizontalVectors p \<and> Y \<in> HorizontalVectors p}"
        using `X \<in> HorizontalVectors p` by blast
    qed
  qed
  then show ?thesis
    unfolding ambrose_singer by simp
qed

end
