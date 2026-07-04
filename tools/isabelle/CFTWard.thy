theory CFTWard
  imports Complex_Main
begin

lemma cft_2pt_identity:
  fixes C z1 z2 Delta1 Delta2 :: real
  assumes "C * (z1 - z2) * (Delta1 - Delta2) = 0"
      and "C \<noteq> 0"
      and "z1 - z2 \<noteq> 0"
  shows "Delta1 = Delta2"
  using assms by auto

end
