theory LlewellynZr79MED
  imports Complex_Main
begin

definition Tz :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "Tz N Z = (N - Z) / 2"

lemma Zr79_Y79_Tz:
  "Tz 39 40 = -1 / 2 \<and> Tz 40 39 = 1 / 2"
  by (simp add: Tz_def; normalization)

definition MED :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "MED excitation_tz_neg_half excitation_tz_pos_half =
    excitation_tz_neg_half - excitation_tz_pos_half"

definition level_from_transition :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "level_from_transition lower gamma = lower + gamma"

lemma MED_7_2_exact:
  "MED 184 183 = 1"
  by (simp add: MED_def; normalization)

lemma MED_9_2_exact:
  "MED 416 411 = 5"
  by (simp add: MED_def; normalization)

lemma MED_11_2_exact:
  "MED 715 726 = -11"
  by (simp add: MED_def; normalization)

lemma MED_13_2_exact:
  "MED 1042 1042 = 0"
  by (simp add: MED_def; normalization)

lemma Y79_cascade_cross_over_discrepancy:
  "level_from_transition 183 227 - 411 = -1"
  by (simp add: level_from_transition_def; normalization)

lemma Zr79_cascade_cross_over_discrepancy:
  "level_from_transition 184 230 - 416 = -2"
  by (simp add: level_from_transition_def; normalization)

lemma beta_ordering:
  "(294 / 1000 :: rat) < 296 / 1000 \<and>
    (296 / 1000 :: rat) < 304 / 1000 \<and>
    (298 / 1000 :: rat) < 304 / 1000"
  by normalization

lemma selected_to_mixing_configurations:
  "(10 * 4 :: nat) = 40"
  by simp

end
