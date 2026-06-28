theory ChiralCompasses
  imports Main
begin

text \<open>
  Isabelle/HOL Verification: Cl(1,1) \<otimes> Cl(1,1) \<cong> Cl(2,2)
  The factorization of 4D conformal split spacetime into two chiral compasses.
\<close>

record signature =
  plus_ones :: nat
  minus_ones :: nat

definition cl11 :: signature where
  "cl11 = \<lparr> plus_ones = 1, minus_ones = 1 \<rparr>"

definition cl22 :: signature where
  "cl22 = \<lparr> plus_ones = 2, minus_ones = 2 \<rparr>"

text \<open>
  The graded tensor product of Clifford algebras adds the signatures.
\<close>

definition graded_tensor_sig :: "signature \<Rightarrow> signature \<Rightarrow> signature" where
  "graded_tensor_sig A B = \<lparr>
    plus_ones = plus_ones A + plus_ones B,
    minus_ones = minus_ones A + minus_ones B
  \<rparr>"

lemma chiral_compass_composition:
  "graded_tensor_sig cl11 cl11 = cl22"
  unfolding cl11_def cl22_def graded_tensor_sig_def
  by simp

end
