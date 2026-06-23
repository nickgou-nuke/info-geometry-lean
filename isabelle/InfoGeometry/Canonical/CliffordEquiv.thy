theory CliffordEquiv
  imports Complex_Main
begin

locale complex_algebra =
  fixes add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)
    and mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
    and smul :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
    and S :: 'a
    and one :: 'a
  assumes S_sq: "S * S = smul (-1) one"
begin

definition to_complex :: "real \<Rightarrow> real \<Rightarrow> 'a" where
  "to_complex r s = smul r one + smul s S"

end

text \<open>Honest boundary: Clifford-Peirce isomorphisms are isomorphic to Complex via to_complex mapping.\<close>

end
