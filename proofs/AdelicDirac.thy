theory AdelicDirac
  imports Main Complex_Main
begin

definition maximal_isotropy :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "maximal_isotropy D D_dagger I \<longleftrightarrow> D - I/2 = -(D_dagger - I/2)"

lemma symmetric_part_shift:
  fixes D D_dagger I :: real
  assumes "maximal_isotropy D D_dagger I"
  shows "D + D_dagger = I"
  using assms unfolding maximal_isotropy_def by auto

end
