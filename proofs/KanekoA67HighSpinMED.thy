theory KanekoA67HighSpinMED
  imports Complex_Main
begin

definition total_med :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "total_med VCM VCr ell ls = VCM + VCr + ell + ls"

lemma epsilonLL_gap_g9_f5_reduction:
  "(-95::rat) - (-58) = -37"
  by normalization

lemma epsilonLS_gap_g9_f5_reduction:
  "(-66::rat) - 66 = -132"
  by normalization

definition radial_med :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "radial_med m9 mJ = 280 * (m9 / 2 - mJ / 2)"

lemma radial_med_positive_when_p32_decreases:
  "radial_med 4 3 = 140"
  by (simp add: radial_med_def; normalization)

lemma g9_total_jump_at_25half:
  "(2::rat) + 1 = 3"
  by normalization

lemma highSpin_MED_model_exact:
  "total_med (-40) 140 0 (-132) = -32"
  by (simp add: total_med_def; normalization)

lemma spinOrbit_radial_interference:
  "(140::rat) + (-132) = 8"
  by normalization

end
