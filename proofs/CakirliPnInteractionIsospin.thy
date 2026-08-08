theory CakirliPnInteractionIsospin
  imports Complex_Main
begin

definition Tz :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "Tz N Z = (N - Z) / 2"

lemma Tz_mirror_negates:
  "Tz Z N = - Tz N Z"
  by (simp add: Tz_def; algebra)

lemma Tz_A23_Na_Mg:
  "Tz 12 11 = 1 / 2 \<and> Tz 11 12 = -1 / 2"
  by (simp add: Tz_def; normalization)

definition binding_energy :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "binding_energy Z N mp mn M c2 = (Z * mp + N * mn - M) * c2"

definition mirror_delta :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "mirror_delta delta_tz_neg_half delta_tz_pos_half =
    delta_tz_neg_half - delta_tz_pos_half"

definition near_zero_band :: "rat \<Rightarrow> bool" where
  "near_zero_band x \<longleftrightarrow> abs x \<le> 50"

lemma A7_delta_exact:
  "mirror_delta 5785 5970 = -185"
  by (simp add: mirror_delta_def; normalization)

lemma A9_delta_exact:
  "mirror_delta 914 1037 = -123"
  by (simp add: mirror_delta_def; normalization)

lemma A13_delta_within_error:
  "abs (mirror_delta 1661 2222 - (-562)) \<le> 3"
  by (simp add: mirror_delta_def; normalization)

lemma A15_delta_exact:
  "mirror_delta (41384 / 10) (41320 / 10) = 64 / 10"
  by (simp add: mirror_delta_def; normalization)

lemma A17_delta_within_error:
  "abs (mirror_delta 935 (14625 / 10) - (-527)) \<le> 7"
  by (simp add: mirror_delta_def; normalization)

lemma A19_delta_within_error:
  "abs (mirror_delta (37467 / 10) (36966 / 10) - (500 / 10)) \<le> 3 / 10"
  by (simp add: mirror_delta_def; normalization)

lemma A23_delta_exact:
  "mirror_delta (31920 / 10) (318140 / 100) = 106 / 10"
  by (simp add: mirror_delta_def; normalization)

lemma A25_delta_near_zero:
  "near_zero_band (mirror_delta (10650 / 10) (10650 / 10))"
  by (simp add: near_zero_band_def mirror_delta_def; normalization)

lemma A13_outside_50keV_band:
  "\<not> near_zero_band (mirror_delta 1661 2222)"
  by (simp add: near_zero_band_def mirror_delta_def; normalization)

lemma large_bar_mod4:
  "7 mod 4 = (3::nat) \<and> 11 mod 4 = (3::nat) \<and>
    15 mod 4 = (3::nat) \<and> 19 mod 4 = (3::nat)"
  by simp

lemma small_bar_mod4:
  "9 mod 4 = (1::nat) \<and> 13 mod 4 = (1::nat) \<and>
    17 mod 4 = (1::nat) \<and> 21 mod 4 = (1::nat)"
  by simp

end
