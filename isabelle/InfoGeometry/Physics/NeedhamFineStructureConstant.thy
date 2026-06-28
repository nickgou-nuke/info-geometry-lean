theory NeedhamFineStructureConstant
  imports Complex_Main
begin

definition phi :: real where
  "phi = (1 + sqrt 5) / 2"

definition needham_alpha_inverse :: real where
  "needham_alpha_inverse = 10 * pi * phi * exp 1 - ln pi"

definition codata2018_alpha_inverse :: real where
  "codata2018_alpha_inverse = 137.035999084"

definition needham_abs_error :: real where
  "needham_abs_error = abs (needham_alpha_inverse - codata2018_alpha_inverse)"

definition needham_rel_error :: real where
  "needham_rel_error = needham_abs_error / codata2018_alpha_inverse"

lemma phi_sq : "phi^2 = phi + 1"
  unfolding phi_def
  by (simp add: field_simps power2_eq_square)

lemma phi_pos : "0 < phi"
proof -
  have hs : "0 < sqrt 5" by simp
  have h1 : "0 < 1 + sqrt 5" using hs by linarith
  show ?thesis
    unfolding phi_def
    using h1 by (simp add: divide_pos_pos)
qed

lemma needham_alpha_inverse_eq_closed_form :
  "needham_alpha_inverse = 5 * pi * (1 + sqrt 5) * exp 1 - ln pi"
  unfolding needham_alpha_inverse_def phi_def
  by (simp add: field_simps)

lemma codata2018_alpha_inverse_pos : "0 < codata2018_alpha_inverse"
  unfolding codata2018_alpha_inverse_def
  by simp

lemma needham_abs_error_nonneg : "0 <= needham_abs_error"
proof -
  have h : "0 <= abs (needham_alpha_inverse - codata2018_alpha_inverse)" by simp
  show ?thesis
    unfolding needham_abs_error_def using h by simp
qed

lemma needham_rel_error_nonneg : "0 <= needham_rel_error"
proof -
  have h1 : "0 <= needham_abs_error" using needham_abs_error_nonneg .
  have h2 : "0 < codata2018_alpha_inverse" using codata2018_alpha_inverse_pos .
  show ?thesis
    unfolding needham_rel_error_def
    using h1 h2 by (simp add: divide_nonneg_nonneg)
qed

end
