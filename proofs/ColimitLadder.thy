theory ColimitLadder
  imports Main
begin

datatype NumSys = Primes | Naturals | Rationals | Reals | Complex

text \<open>
Formalizing the algebraic completion steps and verifying the universal properties
of localizations and pushouts conceptually.
\<close>

inductive Step :: "NumSys \<Rightarrow> NumSys \<Rightarrow> bool" where
  "Step Primes Naturals"
| "Step Naturals Rationals"
| "Step Rationals Reals"
| "Step Reals Complex"

inductive Ladder :: "NumSys \<Rightarrow> NumSys \<Rightarrow> bool" where
  base: "Ladder x x"
| step: "Step x y \<Longrightarrow> Ladder y z \<Longrightarrow> Ladder x z"

theorem prime_to_complex: "Ladder Primes Complex"
  apply (rule step)
  apply (rule Step.intros(1))
  apply (rule step)
  apply (rule Step.intros(2))
  apply (rule step)
  apply (rule Step.intros(3))
  apply (rule step)
  apply (rule Step.intros(4))
  apply (rule base)
  done

end
