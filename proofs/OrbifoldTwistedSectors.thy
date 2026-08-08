theory OrbifoldTwistedSectors
  imports Main
begin

text \<open>Formulation of the $T^5 / \mathbb{Z}_2$ orbifold factor space and the twisted string states localized at singular fixed points.\<close>

typedecl Torus5
typedecl Z2Action

axiomatization
  action :: "Z2Action \<Rightarrow> Torus5 \<Rightarrow> Torus5" and
  is_fixed_point :: "Torus5 \<Rightarrow> bool"
where
  fixed_point_def: "is_fixed_point x \<longleftrightarrow> (\<exists> g. action g x = x)"

typedecl TwistedStringState

axiomatization
  localize :: "TwistedStringState \<Rightarrow> Torus5" and
  is_twisted_sector :: "TwistedStringState \<Rightarrow> bool"
where
  localization_rule: "is_twisted_sector s \<Longrightarrow> is_fixed_point (localize s)"

lemma twisted_state_localized:
  assumes "is_twisted_sector s"
  shows "is_fixed_point (localize s)"
  using assms localization_rule by simp

end
