theory SpaceTimeOrientation
  imports Main
begin

section \<open>Space/Time Orientability Characters\<close>

text \<open>
  We define space and time orientability as sections over a topological space,
  representing the continuous choice of orientation for space-like and time-like
  subspaces in a pseudo-Riemannian manifold context.
\<close>

typedecl M

datatype orientation = Pos | Neg

type_synonym orientation_section = "M \<Rightarrow> orientation"

definition total_orientation :: "orientation_section \<Rightarrow> orientation_section \<Rightarrow> orientation_section" where
  "total_orientation s_plus s_minus = (\<lambda>x. if s_plus x = s_minus x then Pos else Neg)"

lemma total_orientation_sym:
  "total_orientation s_plus s_minus = total_orientation s_minus s_plus"
  unfolding total_orientation_def by auto

end
