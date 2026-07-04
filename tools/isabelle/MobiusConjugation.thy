theory MobiusConjugation
  imports Complex_Main
begin

definition circle_inversion :: "complex \<Rightarrow> real \<Rightarrow> complex \<Rightarrow> complex" where
  "circle_inversion z0 r z = z0 + (of_real r)^2 / cnj (z - z0)"

lemma circle_inversion_involution:
  assumes "z \<noteq> z0" and "r \<noteq> 0"
  shows "circle_inversion z0 r (circle_inversion z0 r z) = z"
  using assms
  unfolding circle_inversion_def
  by simp

end
