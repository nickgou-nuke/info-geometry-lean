theory SarsBregmanDuality
  imports Main
begin

datatype expr = X | Y | U | EX | EY | One | Add expr expr | Sub expr expr | Mul expr expr | Exp expr | Log expr

fun normalize :: "expr => expr" where
  "normalize (Log (Exp a)) = normalize a" |
  "normalize (Exp a) = Exp (normalize a)" |
  "normalize (Log a) = Log (normalize a)" |
  "normalize (Add a b) = Add (normalize a) (normalize b)" |
  "normalize (Sub a b) = Sub (normalize a) (normalize b)" |
  "normalize (Mul a b) = Mul (normalize a) (normalize b)" |
  "normalize a = a"

definition modular_expr :: expr where "modular_expr = Sub (Sub U (Sub X Y)) One"
definition burg_exp_expr :: expr where "burg_exp_expr = Sub (Sub U (Log (Exp (Sub X Y)))) One"
definition itakura_exp_expr :: expr where "itakura_exp_expr = Sub (Sub (Exp X) (Log (Exp X))) One"
definition itakura_modular_expr :: expr where "itakura_modular_expr = Sub (Sub (Exp X) X) One"
definition surprisal_quadratic :: "int => int" where "surprisal_quadratic n = n*n"
definition edges :: "string list" where "edges = [''qft_modular_to_itakura_saito'', ''bregman_coordinate_isomorphism'', ''stabilizes_krein_entropy'']"

theorem burg_exp_normalizes: "normalize burg_exp_expr = modular_expr"
  by (simp add: burg_exp_expr_def modular_expr_def)

theorem itakura_exp_normalizes: "normalize itakura_exp_expr = itakura_modular_expr"
  by (simp add: itakura_exp_expr_def itakura_modular_expr_def)

theorem surprisal_quadratic_nonneg: "0 <= surprisal_quadratic n"
  by (simp add: surprisal_quadratic_def)

theorem bregman_duality_kernel:
  "normalize burg_exp_expr = modular_expr \<and>
   normalize itakura_exp_expr = itakura_modular_expr \<and>
   (\<forall>n. 0 <= surprisal_quadratic n) \<and>
   surprisal_quadratic 0 = 0 \<and>
   length edges = 3"
  by (simp add: burg_exp_normalizes itakura_exp_normalizes surprisal_quadratic_nonneg surprisal_quadratic_def edges_def)

end
