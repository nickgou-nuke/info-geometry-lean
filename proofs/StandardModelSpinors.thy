theory StandardModelSpinors
  imports Main
begin

definition spinor_dim :: nat where
  "spinor_dim = 32"

definition weyl_plus_dim :: nat where
  "weyl_plus_dim = 16"

definition weyl_minus_dim :: nat where
  "weyl_minus_dim = 16"

lemma spinor_split: "spinor_dim = weyl_plus_dim + weyl_minus_dim"
  unfolding spinor_dim_def weyl_plus_dim_def weyl_minus_dim_def
  by simp

end
