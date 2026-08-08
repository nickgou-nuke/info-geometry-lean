theory SarsCasimirSpring
  imports Main
begin

definition casimir_on_shell :: "int => int" where "casimir_on_shell m = - (m*m)"
definition stiffness_from_casimir :: "int => int" where "stiffness_from_casimir C = -C"
definition mass_stiffness :: "int => int" where "mass_stiffness m = m*m"
definition spring_potential_abs_mass :: "int => int => int" where "spring_potential_abs_mass m lam = abs (m*lam)"
definition restoring_force_mass :: "int => int => int" where "restoring_force_mass m lam = -m*m*lam"
definition dilation_casimir_bracket :: "int => int" where "dilation_casimir_bracket C = 2*C"

datatype concept = Poincare_Casimir_On_Shell | Mass_Shell_Coadjoint_Orbit | Souriau_Entropic_Leaf | Conformal_Dilation_Spring | Dilaton_Transverse_Flow | Compton_Equilibrium_Scale
datatype edge = labels | identical_to | gives_stiffness | resists | crosses | restores_to
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Poincare_Casimir_On_Shell labels Mass_Shell_Coadjoint_Orbit = True" |
  "edgeHolds Mass_Shell_Coadjoint_Orbit identical_to Souriau_Entropic_Leaf = True" |
  "edgeHolds Poincare_Casimir_On_Shell gives_stiffness Conformal_Dilation_Spring = True" |
  "edgeHolds Conformal_Dilation_Spring resists Dilaton_Transverse_Flow = True" |
  "edgeHolds Dilaton_Transverse_Flow crosses Souriau_Entropic_Leaf = True" |
  "edgeHolds Conformal_Dilation_Spring restores_to Compton_Equilibrium_Scale = True" |
  "edgeHolds _ _ _ = False"

theorem casimir_spring_kernel:
  "(\<forall>m. stiffness_from_casimir (casimir_on_shell m) = mass_stiffness m) \<and>
   mass_stiffness 0 = 0 \<and>
   (\<forall>m. 0 <= mass_stiffness m) \<and>
   (\<forall>m lam. 0 <= spring_potential_abs_mass m lam) \<and>
   (\<forall>m. spring_potential_abs_mass m 0 = 0) \<and>
   (\<forall>C. dilation_casimir_bracket C = 2*C)"
  by (simp add: casimir_on_shell_def stiffness_from_casimir_def mass_stiffness_def spring_potential_abs_mass_def dilation_casimir_bracket_def)

theorem casimir_spring_graph_kernel:
  "edgeHolds Poincare_Casimir_On_Shell labels Mass_Shell_Coadjoint_Orbit = True \<and>
   edgeHolds Mass_Shell_Coadjoint_Orbit identical_to Souriau_Entropic_Leaf = True \<and>
   edgeHolds Poincare_Casimir_On_Shell gives_stiffness Conformal_Dilation_Spring = True \<and>
   edgeHolds Conformal_Dilation_Spring resists Dilaton_Transverse_Flow = True \<and>
   edgeHolds Dilaton_Transverse_Flow crosses Souriau_Entropic_Leaf = True \<and>
   edgeHolds Conformal_Dilation_Spring restores_to Compton_Equilibrium_Scale = True"
  by simp

end
