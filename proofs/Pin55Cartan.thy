theory Pin55Cartan
  imports Main
begin

text ‹Cartan Involution and Projectors algebraically for Pin(5,5)›

locale Pin55_Cartan =
  fixes J :: "'a ⇒ 'a"
  and P_plus :: "'a ⇒ 'a"
  and P_minus :: "'a ⇒ 'a"
  and add :: "'a ⇒ 'a ⇒ 'a" (infixl "⊕" 65)
  and zero :: "'a" ("𝟬")
  and smul :: "real ⇒ 'a ⇒ 'a" (infixr "⊙" 70)
  assumes J_linear: "J (x ⊕ y) = J x ⊕ J y"
      and J_smul: "J (c ⊙ x) = c ⊙ J x"
      and J_inv: "J (J x) = x"
      and P_plus_def: "P_plus x = (1/2) ⊙ (x ⊕ J x)"
      and P_minus_def: "P_minus x = (1/2) ⊙ (x ⊕ (-1) ⊙ J x)"
begin

lemma J_P_plus: "J (P_plus x) = P_plus x"
  sorry

lemma J_P_minus: "J (P_minus x) = (-1) ⊙ (P_minus x)"
  sorry

end

end
