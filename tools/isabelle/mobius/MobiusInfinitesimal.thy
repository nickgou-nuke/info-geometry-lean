theory MobiusInfinitesimal
  imports Complex_Main
begin

type_synonym sl2_triple = "complex * complex * complex"

definition vector_field :: "sl2_triple => complex => complex" where
  "vector_field M z =
    (let a = fst M; bc = snd M; b = fst bc; c = snd bc
     in - c * z^2 + 2 * a * z + b)"

definition discriminant :: "sl2_triple => complex" where
  "discriminant M =
    (let a = fst M; bc = snd M; b = fst bc; c = snd bc
     in 4 * a^2 + 4 * b * c)"

definition matrix_det :: "sl2_triple => complex" where
  "matrix_det M =
    (let a = fst M; bc = snd M; b = fst bc; c = snd bc
     in -(a^2) - b * c)"

definition parabolic :: sl2_triple where
  "parabolic = (1, 1, -1)"

definition hyperbolic :: sl2_triple where
  "hyperbolic = (1, 0, -1)"

definition elliptic :: sl2_triple where
  "elliptic = (0, 1, -1)"

theorem discriminant_eq_neg_four_det:
  "discriminant M = -4 * matrix_det M"
  by (cases M) (auto simp add: discriminant_def matrix_det_def algebra_simps)

theorem parabolic_vector_field:
  "vector_field parabolic z = z^2 + 2 * z + 1"
  by (simp add: vector_field_def parabolic_def algebra_simps)

theorem hyperbolic_vector_field:
  "vector_field hyperbolic z = z^2 + 2 * z"
  by (simp add: vector_field_def hyperbolic_def algebra_simps)

theorem elliptic_vector_field:
  "vector_field elliptic z = z^2 + 1"
  by (simp add: vector_field_def elliptic_def algebra_simps)

theorem parabolic_discriminant:
  "discriminant parabolic = 0"
  by (simp add: discriminant_def parabolic_def algebra_simps)

theorem hyperbolic_discriminant:
  "discriminant hyperbolic = 4"
  by (simp add: discriminant_def hyperbolic_def algebra_simps)

theorem elliptic_discriminant:
  "discriminant elliptic = -4"
  by (simp add: discriminant_def elliptic_def algebra_simps)

end
