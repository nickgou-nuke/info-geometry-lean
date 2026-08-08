theory CCCInversion
  imports Main
begin

definition is_balanced :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_balanced D D_dagger \<longleftrightarrow> D + D_dagger = 1"

definition InfinityState_D :: int where "InfinityState_D = 1"
definition InfinityState_D_dagger :: int where "InfinityState_D_dagger = 0"

lemma Infinity_is_balanced: "is_balanced InfinityState_D InfinityState_D_dagger"
  unfolding is_balanced_def InfinityState_D_def InfinityState_D_dagger_def
  by simp

definition ZeroState_D :: int where "ZeroState_D = 0"
definition ZeroState_D_dagger :: int where "ZeroState_D_dagger = 1"

lemma Zero_is_balanced: "is_balanced ZeroState_D ZeroState_D_dagger"
  unfolding is_balanced_def ZeroState_D_def ZeroState_D_dagger_def
  by simp

definition conformal_inversion_D :: "int \<Rightarrow> int \<Rightarrow> int" where
  "conformal_inversion_D D D_dagger = D_dagger"

definition conformal_inversion_D_dagger :: "int \<Rightarrow> int \<Rightarrow> int" where
  "conformal_inversion_D_dagger D D_dagger = D"

theorem inversion_preserves_balance:
  assumes "is_balanced D D_dagger"
  shows "is_balanced (conformal_inversion_D D D_dagger) (conformal_inversion_D_dagger D D_dagger)"
  using assms
  unfolding is_balanced_def conformal_inversion_D_def conformal_inversion_D_dagger_def
  by simp

theorem inversion_involution:
  "conformal_inversion_D (conformal_inversion_D D D_dagger) (conformal_inversion_D_dagger D D_dagger) = D"
  "conformal_inversion_D_dagger (conformal_inversion_D D D_dagger) (conformal_inversion_D_dagger D D_dagger) = D_dagger"
  unfolding conformal_inversion_D_def conformal_inversion_D_dagger_def
  by simp_all

theorem inversion_maps_infinity_to_zero:
  "conformal_inversion_D InfinityState_D InfinityState_D_dagger = ZeroState_D"
  "conformal_inversion_D_dagger InfinityState_D InfinityState_D_dagger = ZeroState_D_dagger"
  unfolding conformal_inversion_D_def conformal_inversion_D_dagger_def InfinityState_D_def InfinityState_D_dagger_def ZeroState_D_def ZeroState_D_dagger_def
  by simp_all

end
