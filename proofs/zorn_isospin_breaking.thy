theory ZornIsospinBreaking
  imports Main Complex_Main
begin

text ‹
  Isabelle/HOL formalization of the Zorn Split Octonion Non-Associator.
›

datatype Zorn = Zorn (a: complex) (b: complex)

fun zorn_add :: "Zorn ⇒ Zorn ⇒ Zorn" where
  "zorn_add (Zorn a1 b1) (Zorn a2 b2) = Zorn (a1 + a2) (b1 + b2)"

lemma zorn_add_comm: "zorn_add X Y = zorn_add Y X"
  apply (cases X)
  apply (cases Y)
  apply (simp add: add.commute)
  done

end
