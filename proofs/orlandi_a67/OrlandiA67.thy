theory OrlandiA67 imports Complex_Main begin

definition tauAs :: rat where "tauAs = 7/10"
definition tauSe :: rat where "tauSe = 13/10"
definition BE1As1 :: rat where "BE1As1 = 13/10"
definition BE1Se1 :: rat where "BE1Se1 = 1"
definition BE1As2 :: rat where "BE1As2 = (81/10)/1000000"
definition BE1Se2 :: rat where "BE1Se2 = (17/10)/1000000"

theorem tau_ratio: "tauSe / tauAs = 13/7"
  by (simp add: tauAs_def tauSe_def)

theorem BE1_first_ratio: "BE1As1 / BE1Se1 = 13/10"
  by (simp add: BE1As1_def BE1Se1_def)

theorem BE1_second_ratio: "BE1As2 / BE1Se2 = 81/17"
  by (simp add: BE1As2_def BE1Se2_def)

theorem BE1_second_delta: "BE1As2 - BE1Se2 = (32/5)/1000000"
  by (simp add: BE1As2_def BE1Se2_def)

end
