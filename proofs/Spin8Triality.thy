theory Spin8Triality
  imports Main
begin

datatype Spin8Rep = Vector | SpinorPlus | SpinorMinus

fun rho :: "Spin8Rep \<Rightarrow> Spin8Rep" where
  "rho Vector = SpinorPlus" |
  "rho SpinorPlus = SpinorMinus" |
  "rho SpinorMinus = Vector"

fun sigma :: "Spin8Rep \<Rightarrow> Spin8Rep" where
  "sigma Vector = SpinorPlus" |
  "sigma SpinorPlus = Vector" |
  "sigma SpinorMinus = SpinorMinus"

lemma rho_cubed_id: "rho (rho (rho x)) = x"
  by (cases x) simp_all

lemma sigma_squared_id: "sigma (sigma x) = x"
  by (cases x) simp_all

lemma rho_sigma_rel: "sigma (rho (sigma x)) = rho (rho x)"
  by (cases x) simp_all

end
