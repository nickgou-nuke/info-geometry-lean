theory PolygonConcavity
  imports Main
begin

record Point =
  x :: int
  y :: int

definition orientation_det :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> int" where
  "orientation_det p q r = (x q - x p) * (y r - y p) - (y q - y p) * (x r - x p)"

definition is_collinear :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool" where
  "is_collinear p q r = (orientation_det p q r = 0)"

definition is_convex :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool" where
  "is_convex p q r = (orientation_det p q r > 0)"

definition is_concave :: "Point \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool" where
  "is_concave p q r = (orientation_det p q r < 0)"

lemma collinear_det_zero: "is_collinear p q r \<Longrightarrow> orientation_det p q r = 0"
  by (simp add: is_collinear_def)

end
