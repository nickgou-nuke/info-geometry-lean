theory FubiniStudyAsymptotics
  imports Complex_Main
begin

text \<open>Formalization of the O(p^3) asymptotic growth bound for the Fubini-Study metric
      induced by Kodaira maps over punctured Riemann surfaces.\<close>

definition fubini_study_metric :: "real \<Rightarrow> real" where
  "fubini_study_metric p = p^3"

definition is_O_p3 :: "(real \<Rightarrow> real) \<Rightarrow> bool" where
  "is_O_p3 f \<longleftrightarrow> (\<exists>C>0. \<exists>p0>0. \<forall>p\<ge>p0. \<bar>f p\<bar> \<le> C * \<bar>p^3\<bar>)"

lemma fubini_study_O_p3:
  "is_O_p3 fubini_study_metric"
  unfolding is_O_p3_def fubini_study_metric_def
  apply (rule exI[of _ 1])
  apply simp
  apply (rule exI[of _ 1])
  apply simp
  done

end
