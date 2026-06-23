theory TripotentProjector
  imports Complex_Main
begin

locale tripotent_projector =
  fixes mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)
    and sub :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-" 65)
    and smul :: "real \<Rightarrow> 'a \<Rightarrow> 'a"
    and zero :: 'a
    and one :: 'a
    and OP1 :: 'a
    and OP2 :: 'a
  assumes OP1_proj: "OP1 * OP1 = OP1"
      and OP2_proj: "OP2 * OP2 = OP2"
      and OP_orth: "OP1 * OP2 = zero"
      and OP_orth2: "OP2 * OP1 = zero"
begin

definition T :: 'a where
  "T = OP1 - OP2"

end
end
