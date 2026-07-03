theory G2TwoSplitZorn imports Main begin

definition g2two_order :: nat where "g2two_order = 12096"
definition g2two_derived_order :: nat where "g2two_derived_order = 6048"
definition pgl3f3_order :: nat where "pgl3f3_order = 5616"
definition split_oct_f2_card :: nat where "split_oct_f2_card = 256"

lemma split_oct_f2_card_eq: "split_oct_f2_card = 2 ^ 8"
  by (simp add: split_oct_f2_card_def)

lemma g2two_order_formula: "g2two_order = 2 ^ 6 * (2 ^ 6 - 1) * (2 ^ 2 - 1)"
  by (simp add: g2two_order_def)

lemma derived_half_order: "g2two_derived_order * 2 = g2two_order"
  by (simp add: g2two_derived_order_def g2two_order_def)

lemma pgl3f3_order_ne_g2two_order: "pgl3f3_order \<noteq> g2two_order"
  by (simp add: pgl3f3_order_def g2two_order_def)

end

