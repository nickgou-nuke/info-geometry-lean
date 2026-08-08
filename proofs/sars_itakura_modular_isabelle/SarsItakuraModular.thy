theory SarsItakuraModular
  imports Main
begin

datatype expr = VarX | VarZ | Exp expr | Log expr | One | Sub expr expr

fun normalize :: "expr => expr" where
  "normalize (Log (Exp VarX)) = VarX" |
  "normalize (Exp a) = Exp (normalize a)" |
  "normalize (Log a) = Log (normalize a)" |
  "normalize (Sub a b) = Sub (normalize a) (normalize b)" |
  "normalize a = a"

definition itakura_exp_expr :: expr where
  "itakura_exp_expr = Sub (Sub (Exp VarX) (Log (Exp VarX))) One"
definition modular_reassociated :: expr where
  "modular_reassociated = Sub (Sub (Exp VarX) VarX) One"
definition surprisal_quadratic :: "int => int" where
  "surprisal_quadratic x = x*x"
definition edges :: "string list" where
  "edges = [''exp_coordinate_transform'', ''bregman_dual'', ''stabilizes_modular_flow'']"

theorem log_exp_normalizes: "normalize (Log (Exp VarX)) = VarX"
  by simp

theorem itakura_exp_normal_form: "normalize itakura_exp_expr = modular_reassociated"
  by (simp add: itakura_exp_expr_def modular_reassociated_def)

theorem surprisal_quadratic_nonneg: "0 <= surprisal_quadratic x"
  by (simp add: surprisal_quadratic_def)

theorem itakura_modular_kernel:
  "normalize (Log (Exp VarX)) = VarX \<and>
   normalize itakura_exp_expr = modular_reassociated \<and>
   (\<forall>x. 0 <= surprisal_quadratic x) \<and>
   surprisal_quadratic 0 = 0 \<and>
   length edges = 3"
  by (simp add: itakura_exp_normal_form surprisal_quadratic_nonneg surprisal_quadratic_def edges_def)

end
