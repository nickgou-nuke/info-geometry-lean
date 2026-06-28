theory LogCFT
  imports Complex_Main "InfoGeometry/Canonical/ParabolicClock"
begin

text \<open>Logarithmic CFT Jordan Block Matrix\<close>

definition N_mat :: "Matrix2x2" where
"N_mat = \<lparr> m11 = 0, m12 = 1, m21 = 0, m22 = 0 \<rparr>"

definition id_mat :: "Matrix2x2" where
"id_mat = \<lparr> m11 = 1, m12 = 0, m21 = 0, m22 = 1 \<rparr>"

definition mat_add :: "Matrix2x2 \<Rightarrow> Matrix2x2 \<Rightarrow> Matrix2x2" where
"mat_add A B = \<lparr> m11 = m11 A + m11 B, m12 = m12 A + m12 B, m21 = m21 A + m21 B, m22 = m22 A + m22 B \<rparr>"

definition mat_smul :: "real \<Rightarrow> Matrix2x2 \<Rightarrow> Matrix2x2" where
"mat_smul c A = \<lparr> m11 = c * m11 A, m12 = c * m12 A, m21 = c * m21 A, m22 = c * m22 A \<rparr>"

definition L0_mat :: "real \<Rightarrow> Matrix2x2" where
"L0_mat h = mat_add (mat_smul h id_mat) N_mat"

theorem L0_is_jordan:
  "L0_mat h = \<lparr> m11 = h, m12 = 1, m21 = 0, m22 = h \<rparr>"
  by (simp add: L0_mat_def mat_add_def mat_smul_def id_mat_def N_mat_def)

end
