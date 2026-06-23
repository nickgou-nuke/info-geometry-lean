theory TestSledgehammer
  imports Complex_Main
begin

lemma test_lemma:
  fixes x :: real
  shows "x + x = 2 * x"
  sledgehammer
  oops

end
