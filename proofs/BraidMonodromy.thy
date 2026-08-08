theory BraidMonodromy
  imports Main Complex_Main
begin

definition zero_mode :: "complex" where
  "zero_mode = 1"

definition braid_action :: "complex \<Rightarrow> complex" where
  "braid_action z = \<i> * pi * z"

definition phase_quantization :: "complex \<Rightarrow> bool" where
  "phase_quantization z \<longleftrightarrow> z = \<i> * pi"

lemma braid_group_action_on_zero_mode:
  "phase_quantization (braid_action zero_mode)"
  unfolding zero_mode_def braid_action_def phase_quantization_def
  by simp

end
