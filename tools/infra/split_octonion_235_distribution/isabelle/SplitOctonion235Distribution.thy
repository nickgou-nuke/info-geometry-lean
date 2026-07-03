theory SplitOctonion235Distribution imports Main begin

definition imaginary_dimension :: nat where "imaginary_dimension = 7"
definition left_annihilator_rank :: nat where "left_annihilator_rank = 4"
definition left_annihilator_dimension :: nat where
  "left_annihilator_dimension = imaginary_dimension - left_annihilator_rank"
definition projectivized_distribution_rank :: nat where
  "projectivized_distribution_rank = left_annihilator_dimension - 1"
definition projective_null_quadric_dimension :: nat where "projective_null_quadric_dimension = 5"
definition first_derived_rank :: nat where "first_derived_rank = 3"
definition ambient_rank :: nat where "ambient_rank = 5"
definition split_g2_symmetry_dimension :: nat where "split_g2_symmetry_dimension = 14"

lemma split_octonion_235_packet:
  "left_annihilator_dimension = 3 \<and>
   projectivized_distribution_rank = 2 \<and>
   first_derived_rank = 3 \<and>
   ambient_rank = 5 \<and>
   projective_null_quadric_dimension = 5 \<and>
   split_g2_symmetry_dimension = 14"
  by (simp add: imaginary_dimension_def left_annihilator_rank_def left_annihilator_dimension_def
    projectivized_distribution_rank_def first_derived_rank_def ambient_rank_def
    projective_null_quadric_dimension_def split_g2_symmetry_dimension_def)

end
