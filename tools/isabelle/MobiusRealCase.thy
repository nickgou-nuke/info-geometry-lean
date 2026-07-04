theory MobiusRealCase
  imports Main
begin

lemma trace_squared_nonneg:
  fixes a d :: "'a::linordered_field"
  shows "0 \<le> (a + d)^2"
  by simp

end
