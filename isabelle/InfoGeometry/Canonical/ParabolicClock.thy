theory ParabolicClock
  imports Complex_Main
begin

text \<open>Parabolic Clock Nilpotent Limit on the Krein Boundary\<close>

record Matrix2x2 =
  m11 :: real
  m12 :: real
  m21 :: real
  m22 :: real

definition mat_mul :: "Matrix2x2 \<Rightarrow> Matrix2x2 \<Rightarrow> Matrix2x2" where
"mat_mul A B = \<lparr>
  m11 = m11 A * m11 B + m12 A * m21 B,
  m12 = m11 A * m12 B + m12 A * m22 B,
  m21 = m21 A * m11 B + m22 A * m21 B,
  m22 = m21 A * m12 B + m22 A * m22 B
\<rparr>"

definition K_mat :: "Matrix2x2" where
"K_mat = \<lparr> m11 = 0, m12 = 1, m21 = 0, m22 = 0 \<rparr>"

definition Zero_mat :: "Matrix2x2" where
"Zero_mat = \<lparr> m11 = 0, m12 = 0, m21 = 0, m22 = 0 \<rparr>"

theorem K_squared_is_zero:
  "mat_mul K_mat K_mat = Zero_mat"
  by (simp add: mat_mul_def K_mat_def Zero_mat_def)

end
