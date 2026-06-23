theory Test
  imports Complex_Main
begin

definition test :: "nat ⇒ int" where
  "test n = (if even n then 1 else -1)"

lemma test_mult: "test (n * m) = test n * test m"
  sorry

end
