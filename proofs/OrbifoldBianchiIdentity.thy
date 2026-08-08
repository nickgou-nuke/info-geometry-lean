theory OrbifoldBianchiIdentity
  imports Main
begin

text \<open>
  Formalization of the modified Bianchi identity and G-flux integral 
  for the T^5 / Z_2 orbifold.
\<close>

typedecl boundary
typedecl flux

consts
  integrate_flux :: "flux \<Rightarrow> boundary \<Rightarrow> real"
  anomaly_inflow :: "boundary \<Rightarrow> real"
  G_flux :: flux
  orbifold_boundary :: boundary

axiomatization where
  modified_bianchi_identity: "integrate_flux G_flux orbifold_boundary + anomaly_inflow orbifold_boundary = 0"

theorem global_topological_requirement:
  "integrate_flux G_flux orbifold_boundary = - anomaly_inflow orbifold_boundary"
  using modified_bianchi_identity by simp

end
