theory CFTPrimary
  imports Complex_Main
begin

typedecl S

axiomatization
  add :: "S \<Rightarrow> S \<Rightarrow> S" (infixl "+\<^sub>s" 65) and
  sub :: "S \<Rightarrow> S \<Rightarrow> S" (infixl "-\<^sub>s" 65) and
  smult :: "real \<Rightarrow> S \<Rightarrow> S" (infixr "*\<^sub>s" 75) and
  zero :: "S" ("0\<^sub>s") and
  L_1 :: "S \<Rightarrow> S" and
  L0 :: "S \<Rightarrow> S" and
  L1 :: "S \<Rightarrow> S" and
  V :: "S" and
  Delta :: "real"
where
  sub_zero: "x -\<^sub>s 0\<^sub>s = x" and
  L1_L_1_comm: "L1 (L_1 x) -\<^sub>s L_1 (L1 x) = 2 *\<^sub>s (L0 x)" and
  L1_V: "L1 V = 0\<^sub>s" and
  L0_V: "L0 V = Delta *\<^sub>s V" and
  L_1_zero: "L_1 0\<^sub>s = 0\<^sub>s" and
  smult_assoc: "a *\<^sub>s (b *\<^sub>s x) = (a * b) *\<^sub>s x"

lemma primary_descendant: "L1 (L_1 V) = (2 * Delta) *\<^sub>s V"
proof -
  have "L1 (L_1 V) -\<^sub>s L_1 (L1 V) = 2 *\<^sub>s (L0 V)"
    by (simp add: L1_L_1_comm)
  hence "L1 (L_1 V) -\<^sub>s L_1 0\<^sub>s = 2 *\<^sub>s (L0 V)"
    by (simp add: L1_V)
  hence "L1 (L_1 V) -\<^sub>s 0\<^sub>s = 2 *\<^sub>s (L0 V)"
    by (simp add: L_1_zero)
  hence "L1 (L_1 V) = 2 *\<^sub>s (L0 V)"
    by (simp add: sub_zero)
  also have "... = 2 *\<^sub>s (Delta *\<^sub>s V)"
    by (simp add: L0_V)
  also have "... = (2 * Delta) *\<^sub>s V"
    by (simp add: smult_assoc)
  finally show ?thesis .
qed

end
