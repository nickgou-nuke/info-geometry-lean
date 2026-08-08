theory PolygonOrientation
  imports Main
begin

definition orientation_det :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
"orientation_det xA yA xB yB xC yC = (xB * yC + xA * yB + yA * xC) - (yA * xB + yB * xC + xA * yC)"

definition is_counterclockwise :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"is_counterclockwise xA yA xB yB xC yC = (orientation_det xA yA xB yB xC yC > 0)"

definition is_clockwise :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"is_clockwise xA yA xB yB xC yC = (orientation_det xA yA xB yB xC yC < 0)"

definition is_collinear :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"is_collinear xA yA xB yB xC yC = (orientation_det xA yA xB yB xC yC = 0)"

end
