theory Parabolic_Clock_Local
  imports Main
begin

type_synonym mat2 = "int * int * int * int"

definition mat_zero :: mat2 where
  "mat_zero = (0, 0, 0, 0)"

definition mat_one :: mat2 where
  "mat_one = (1, 0, 0, 1)"

definition mat_mul :: "mat2 => mat2 => mat2" where
  "mat_mul A B = (
    let (a11, a12, a21, a22) = A;
        (b11, b12, b21, b22) = B
    in (a11 * b11 + a12 * b21,
        a11 * b12 + a12 * b22,
        a21 * b11 + a22 * b21,
        a21 * b12 + a22 * b22))"

definition mat_det :: "mat2 => int" where
  "mat_det A = (case A of (a11, a12, a21, a22) => a11 * a22 - a12 * a21)"

definition K :: mat2 where
  "K = (0, 1, 0, 0)"

definition parabolic_flow :: "int => mat2" where
  "parabolic_flow t = (1, t, 0, 1)"

lemma K_sq_zero:
  "mat_mul K K = mat_zero"
  by (simp add: K_def mat_mul_def mat_zero_def)

lemma parabolic_flow_det_one:
  "mat_det (parabolic_flow t) = 1"
  by (simp add: parabolic_flow_def mat_det_def)

lemma parabolic_flow_unipotent:
  "parabolic_flow t = (1, t, 0, 1)"
  by (simp add: parabolic_flow_def)

end
