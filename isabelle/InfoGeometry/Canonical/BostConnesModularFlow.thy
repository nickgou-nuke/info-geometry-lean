theory BostConnesModularFlow
  imports Complex_Main
begin

locale bost_connes =
  fixes smul :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
    and generator :: 'a
    and t_flow :: real
    and grading :: real
    and sigma_t :: "'a \<Rightarrow> 'a"
    and Gamma :: "'a \<Rightarrow> 'a"
  assumes sigma_t_smul: "sigma_t (smul r x) = smul r (sigma_t x)"
      and Gamma_smul: "Gamma (smul r x) = smul r (Gamma x)"
      and sigma_t_gen: "sigma_t generator = smul t_flow generator"
      and Gamma_gen: "Gamma generator = smul grading generator"
      and smul_assoc: "smul a (smul b x) = smul (a * b) x"
begin

theorem witten_index_conserved:
  "Gamma (sigma_t generator) = sigma_t (Gamma generator)"
proof -
  have "Gamma (sigma_t generator) = Gamma (smul t_flow generator)" by (simp add: sigma_t_gen)
  also have "... = smul t_flow (Gamma generator)" by (simp add: Gamma_smul)
  also have "... = smul t_flow (smul grading generator)" by (simp add: Gamma_gen)
  also have "... = smul (t_flow * grading) generator" by (simp add: smul_assoc)
  also have "... = smul (grading * t_flow) generator" by (simp add: mult.commute)
  also have "... = smul grading (smul t_flow generator)" by (simp add: smul_assoc [symmetric])
  also have "... = smul grading (sigma_t generator)" by (simp add: sigma_t_gen [symmetric])
  also have "... = sigma_t (smul grading generator)" by (simp add: sigma_t_smul [symmetric])
  also have "... = sigma_t (Gamma generator)" by (simp add: Gamma_gen [symmetric])
  finally show ?thesis .
qed

end
end
