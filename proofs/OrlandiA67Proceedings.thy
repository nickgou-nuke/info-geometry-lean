theory OrlandiA67Proceedings
  imports Complex_Main
begin

definition centroid_shift_time :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "centroid_shift_time c_forward c_reverse =
    ((c_reverse - c_forward) * (56 / 100)) / 2"

lemma raw_centroid_lifetime_As67_943_725:
  "centroid_shift_time (409497 / 100) (409805 / 100) = 1078 / 1250"
  by (simp add: centroid_shift_time_def; normalization)

lemma branching_Se67_sum:
  "(10 / 100 :: rat) + 84 / 100 + 6 / 100 = 1"
  by normalization

lemma BE1_first_ratio_prelim:
  "(13 / 10 :: rat) / 1 = 13 / 10"
  by normalization

lemma BE1_second_ratio_prelim:
  "(81 / 10 :: rat) / (17 / 10) = 81 / 17"
  by normalization

lemma first_pair_near_symmetric:
  "abs ((13 / 10 :: rat) / 1 - 1) \<le> 3 / 10"
  by normalization

lemma second_pair_asymmetric:
  "(4 :: rat) < (81 / 10) / (17 / 10)"
  by normalization

lemma As67_not_12ns_centroid_scale:
  "(7 / 10 :: rat) < 12 / 4"
  by normalization

end
