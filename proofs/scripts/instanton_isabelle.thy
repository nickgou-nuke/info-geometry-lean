theory InstantonLiquid
imports Complex_Main
begin

record QCD_Vacuum =
  T :: real
  rho_bar :: real
  chiral_sym_broken :: bool

definition debye_screening :: "real \<Rightarrow> real \<Rightarrow> bool" where
  "debye_screening T rho_bar \<equiv> T > 150 \<longrightarrow> rho_bar < 0.33"

axiomatization where
  cooling_preserves_topology: "rho_bar > 0.2 \<Longrightarrow> chiral_sym_broken = True"

end
