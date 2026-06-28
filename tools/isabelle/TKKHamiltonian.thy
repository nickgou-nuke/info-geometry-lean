theory TKKHamiltonian
  imports Main Real
begin

text \<open>
  Isabelle/HOL Verification: TKK Hamiltonian and Isospin Projection
\<close>

record state_weight =
  N_protons :: real
  Z_neutrons :: real

definition isospin_I3 :: "state_weight \<Rightarrow> real" where
  "isospin_I3 psi = (N_protons psi - Z_neutrons psi) / 2"

text \<open>
  TKK Hamiltonian Operators
\<close>

record operators =
  N_osc :: real
  C2_SO8 :: real
  Pi_triality :: real

definition H_TKK :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> operators \<Rightarrow> real" where
  "H_TKK omega A Delta ops = 
    omega * N_osc ops + A * C2_SO8 ops + Delta * Pi_triality ops"

lemma isospin_asymmetry:
  "N_protons psi \<noteq> Z_neutrons psi \<Longrightarrow> isospin_I3 psi \<noteq> 0"
  unfolding isospin_I3_def
  by auto

end
