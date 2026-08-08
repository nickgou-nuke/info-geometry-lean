theory PrigoginePhaseTransition
  imports Complex_Main
begin

(* Prigogine thermodynamic engine properties *)
(* Non-equilibrium steady state stability constraint *)

definition entropy_production :: "real ⇒ real ⇒ real" where
  "entropy_production J X = J * X"

(* In non-equilibrium thermodynamics, the steady state is characterized by minimal entropy production *)
definition is_steady_state :: "(real ⇒ real) ⇒ (real ⇒ real) ⇒ real ⇒ bool" where
  "is_steady_state J X t longleftrightarrow (∀t'. entropy_production (J t) (X t) ≤ entropy_production (J t') (X t'))"

theorem prigogine_min_entropy_production:
  assumes "is_steady_state J X t"
  shows "entropy_production (J t) (X t) ≤ entropy_production (J t') (X t')"
using assms by (simp add: is_steady_state_def)

end
