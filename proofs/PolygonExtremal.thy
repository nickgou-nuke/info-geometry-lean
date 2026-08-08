theory PolygonExtremal
  imports Complex_Main
begin

definition is_lex_min :: "(real \<times> real) set \<Rightarrow> (real \<times> real) \<Rightarrow> bool" where
  "is_lex_min S p \<longleftrightarrow> p \<in> S \<and> (\<forall>q \<in> S. fst p < fst q \<or> (fst p = fst q \<and> snd p \<le> snd q))"

definition is_convex_hull_vertex :: "(real \<times> real) set \<Rightarrow> (real \<times> real) \<Rightarrow> bool" where
  "is_convex_hull_vertex S v \<longleftrightarrow> 
    v \<in> S \<and> (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>t::real. 0 < t \<and> t < 1 \<and> v = (t * fst x + (1 - t) * fst y, t * snd x + (1 - t) * snd y) \<longrightarrow> v = x \<or> v = y)"

lemma lex_min_is_extremal:
  assumes "is_lex_min S p"
  shows "is_convex_hull_vertex S p"
  sorry

end
