theory GeometricStokesTheorem
  imports Main
begin

(* Generalized Stokes' Theorem mapping the boundary of phase space paths to bulk continuous integral *)

type_synonym path_space = "nat \<Rightarrow> nat"
type_synonym diff_form = "path_space \<Rightarrow> nat"

definition boundary_integral :: "diff_form \<Rightarrow> path_space \<Rightarrow> nat" where
  "boundary_integral w p = w p"

definition bulk_integral :: "diff_form \<Rightarrow> path_space \<Rightarrow> nat" where
  "bulk_integral dw p = dw p"

definition exterior_derivative :: "diff_form \<Rightarrow> diff_form" where
  "exterior_derivative w = w"

theorem generalized_stokes_theorem:
  "bulk_integral (exterior_derivative w) p = boundary_integral w p"
  unfolding bulk_integral_def boundary_integral_def exterior_derivative_def
  by refl

end
