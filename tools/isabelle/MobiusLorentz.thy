theory MobiusLorentz
  imports Main
begin

type_synonym 'a mat22 = "('a * 'a) * ('a * 'a)"

definition det22 :: "'a::comm_ring_1 mat22 => 'a" where
"det22 m = (case m of ((a, b), (c, d)) => a * d - b * c)"

definition mult22 :: "'a::comm_ring_1 mat22 => 'a mat22 => 'a mat22" where
"mult22 m1 m2 = (case m1 of ((a1, b1), (c1, d1)) => case m2 of ((a2, b2), (c2, d2)) =>
  ((a1 * a2 + b1 * c2, a1 * b2 + b1 * d2),
   (c1 * a2 + d1 * c2, c1 * b2 + d1 * d2)))"

lemma det_mult22: "det22 (mult22 X Y) = det22 X * det22 Y"
  unfolding det22_def mult22_def
  by (auto simp add: algebra_simps split: prod.splits)

lemma det_mult_3: "det22 (mult22 (mult22 A X) B) = det22 A * det22 X * det22 B"
  by (simp add: det_mult22)

lemma det_preserve:
  assumes "det22 A = 1" "det22 B = 1"
  shows "det22 (mult22 (mult22 A X) B) = det22 X"
  by (simp add: det_mult_3 assms)

end
