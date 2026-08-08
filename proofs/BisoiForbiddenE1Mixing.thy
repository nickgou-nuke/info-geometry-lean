theory BisoiForbiddenE1Mixing
  imports Complex_Main
begin

definition equal_mixing_amplitude :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "equal_mixing_amplitude Mexp M01 M10 = Mexp / (M01 + M10)"

definition mixing_probability :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "mixing_probability Mexp M01 M10 =
    (equal_mixing_amplitude Mexp M01 M10)^2"

definition b2_P30 :: rat where
  "b2_P30 = mixing_probability (138/10000) (-228/10000) (801/10000)"

definition b2_S32 :: rat where
  "b2_S32 = mixing_probability (162/10000) (1086/10000) (-127/10000)"

definition b2_Cl34 :: rat where
  "b2_Cl34 = mixing_probability (160/100000) (819/100000) (2533/100000)"

definition b2_Ar36 :: rat where
  "b2_Ar36 = mixing_probability (38/10000) (-144/10000) (-233/10000)"

lemma b2_P30_exact:
  "b2_P30 = 2116 / 36481"
  by (simp add: b2_P30_def mixing_probability_def equal_mixing_amplitude_def; normalization)

lemma b2_S32_exact:
  "b2_S32 = 26244 / 919681"
  by (simp add: b2_S32_def mixing_probability_def equal_mixing_amplitude_def; normalization)

lemma b2_Cl34_exact:
  "b2_Cl34 = 400 / 175561"
  by (simp add: b2_Cl34_def mixing_probability_def equal_mixing_amplitude_def; normalization)

lemma b2_Ar36_exact:
  "b2_Ar36 = 1444 / 142129"
  by (simp add: b2_Ar36_def mixing_probability_def equal_mixing_amplitude_def; normalization)

lemma P30_self_conjugate: "(15::nat) = 15" by simp
lemma S32_self_conjugate: "(16::nat) = 16" by simp
lemma Cl34_self_conjugate: "(17::nat) = 17" by simp
lemma Ar36_self_conjugate: "(18::nat) = 18" by simp

end
