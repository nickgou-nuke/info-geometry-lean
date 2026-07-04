theory AmbroseSinger
  imports Main
begin

typedecl point
typedecl vector
typedecl param
typedecl loop
typedecl lie_group
typedecl lie_algebra

consts
  base_point :: "loop \<Rightarrow> point"
  contracting_loop :: "point \<Rightarrow> vector \<Rightarrow> vector \<Rightarrow> param \<Rightarrow> loop"
  holonomy :: "loop \<Rightarrow> lie_group"
  curvature :: "point \<Rightarrow> vector \<Rightarrow> vector \<Rightarrow> lie_algebra"
  lie_exp :: "lie_algebra \<Rightarrow> lie_group"
  param_sq :: "param \<Rightarrow> param"
  scale_lie :: "param \<Rightarrow> lie_algebra \<Rightarrow> lie_algebra"
  limit_to_zero :: "(param \<Rightarrow> lie_group) \<Rightarrow> lie_algebra"

axiomatization where
  holonomy_expansion: "\<And>p X Y t. holonomy (contracting_loop p X Y t) = lie_exp (scale_lie (param_sq t) (curvature p X Y))" and
  limit_property: "\<And>Z. limit_to_zero (\<lambda>t. lie_exp (scale_lie (param_sq t) Z)) = Z"

lemma ambrose_singer_contraction:
  fixes p :: point and X :: vector and Y :: vector
  shows "limit_to_zero (\<lambda>t. holonomy (contracting_loop p X Y t)) = curvature p X Y"
  by (simp add: holonomy_expansion limit_property)

end
