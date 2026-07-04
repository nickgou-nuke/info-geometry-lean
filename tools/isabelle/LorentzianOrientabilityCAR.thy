theory LorentzianOrientabilityCAR
  imports Main
begin

section \<open>Lorentzian Orientability and CAR Algebra\<close>

text \<open>
  We define space and time orientability characters as homomorphisms into Z_2.
  Then we map these into a CAR (Canonical Anticommutation Relations) algebra structure.
\<close>

datatype Z2 = Plus | Minus

fun mul_Z2 :: "Z2 \<Rightarrow> Z2 \<Rightarrow> Z2" where
  "mul_Z2 Plus Plus = Plus"
| "mul_Z2 Plus Minus = Minus"
| "mul_Z2 Minus Plus = Minus"
| "mul_Z2 Minus Minus = Plus"

lemma mul_Z2_comm: "mul_Z2 x y = mul_Z2 y x"
  by (cases x; cases y; simp)

lemma mul_Z2_assoc: "mul_Z2 (mul_Z2 x y) z = mul_Z2 x (mul_Z2 y z)"
  by (cases x; cases y; cases z; simp)

text \<open>Space and Time Orientability Character Bundles\<close>

locale Manifold =
  fixes M :: "'m set"

locale Orientability = Manifold +
  fixes w_s :: "'m \<Rightarrow> Z2"  \<comment> \<open>Space orientability character\<close>
  fixes w_t :: "'m \<Rightarrow> Z2"  \<comment> \<open>Time orientability character\<close>

text \<open>CAR Algebra on Chiral Boundaries\<close>

locale CARAlgebra =
  fixes A :: "'a set"
  fixes add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 65)
  fixes mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  fixes anticomm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes anticomm_def: "anticomm x y = (x \<otimes> y) \<oplus> (y \<otimes> x)"

text \<open>Mapping Orientability to CAR Algebra\<close>

locale OrientabilityToCAR = Orientability + CARAlgebra +
  fixes map_s :: "Z2 \<Rightarrow> 'a"
  fixes map_t :: "Z2 \<Rightarrow> 'a"
  assumes map_s_anticomm: "anticomm (map_s x) (map_s y) = map_s (mul_Z2 x y)"
  assumes map_t_anticomm: "anticomm (map_t x) (map_t y) = map_t (mul_Z2 x y)"
  assumes map_st_anticomm: "anticomm (map_s x) (map_t y) = map_s x" \<comment> \<open>Arbitrary relation for consistency check\<close>

lemma (in OrientabilityToCAR) map_s_sym:
  "anticomm (map_s x) (map_s y) = anticomm (map_s y) (map_s x)"
proof -
  have "anticomm (map_s x) (map_s y) = map_s (mul_Z2 x y)" by (simp add: map_s_anticomm)
  also have "... = map_s (mul_Z2 y x)" by (simp add: mul_Z2_comm)
  also have "... = anticomm (map_s y) (map_s x)" by (simp add: map_s_anticomm)
  finally show ?thesis .
qed

lemma (in OrientabilityToCAR) map_t_sym:
  "anticomm (map_t x) (map_t y) = anticomm (map_t y) (map_t x)"
proof -
  have "anticomm (map_t x) (map_t y) = map_t (mul_Z2 x y)" by (simp add: map_t_anticomm)
  also have "... = map_t (mul_Z2 y x)" by (simp add: mul_Z2_comm)
  also have "... = anticomm (map_t y) (map_t x)" by (simp add: map_t_anticomm)
  finally show ?thesis .
qed

end
