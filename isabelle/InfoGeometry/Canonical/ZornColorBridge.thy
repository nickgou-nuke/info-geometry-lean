theory ZornColorBridge
  imports Complex_Main
begin

datatype mersenne_mode = M2 | M3 | M7

definition mode_dimension :: "mersenne_mode \<Rightarrow> nat" where
  "mode_dimension m = (case m of M2 \<Rightarrow> 3 | M3 \<Rightarrow> 7 | M7 \<Rightarrow> 127)"

definition coupling137 :: nat where
  "coupling137 = 137"

record zorn_slot =
  slot_dim :: nat
  is_color :: bool
  is_anticolor :: bool

definition F :: "mersenne_mode \<Rightarrow> zorn_slot" where
  "F m = (case m of
    M2 \<Rightarrow> \<lparr>slot_dim = 3, is_color = True, is_anticolor = False\<rparr>
  | M3 \<Rightarrow> \<lparr>slot_dim = 7, is_color = False, is_anticolor = False\<rparr>
  | M7 \<Rightarrow> \<lparr>slot_dim = 127, is_color = False, is_anticolor = False\<rparr>)"

lemma mode_dimension_M2[simp] : "mode_dimension M2 = 3"
  by (simp add: mode_dimension_def)

lemma mode_dimension_M3[simp] : "mode_dimension M3 = 7"
  by (simp add: mode_dimension_def)

lemma mode_dimension_M7[simp] : "mode_dimension M7 = 127"
  by (simp add: mode_dimension_def)

lemma coupling137_decomposition :
  "coupling137 = mode_dimension M2 + mode_dimension M3 + mode_dimension M7"
  by (simp add: coupling137_def mode_dimension_def)

lemma F_M2_slot_dim : "slot_dim (F M2) = 3"
  by (simp add: F_def)

text \<open>Honest scope boundary: finite 3/7/127 packet only; no SU(3) or G2 classification theorem.\<close>

end
