theory MonadicColimit
  imports Main
begin

text \<open>
  We formalize a Monad over a simple category, specifically a poset
  represented by a complete lattice.
  A functor on this category is a monotone function.
  A monad is a functor with a unit (x <= T x) and multiplication (T (T x) <= T x).
  An algebra is an object x with an evaluation T x <= x.
\<close>

locale poset_monad =
  fixes T :: "'a::complete_lattice => 'a"
  assumes functorial: "x <= y ==> T x <= T y"
      and unit: "x <= T x"
      and mult: "T (T x) <= T x"
begin

definition is_algebra :: "'a => bool" where
  "is_algebra x = (T x <= x)"

text \<open>
  We prove that if the underlying functor T distributes over a supremum (colimit),
  then the colimit of a set of algebras is also an algebra.
  This means the algebraic structure (evaluation) distributes over the limit/colimit,
  i.e., colimits of algebras are created in the base category.
\<close>

lemma algebra_colimit_preservation:
  assumes distributes: "T (Sup X) = Sup (T ` X)"
      and algebras: "\<forall>x\<in>X. is_algebra x"
  shows "is_algebra (Sup X)"
proof -
  have "T (Sup X) = Sup (T ` X)"
    by (rule distributes)
  also have "Sup (T ` X) <= Sup X"
  proof (rule Sup_least)
    fix y
    assume "y \<in> T ` X"
    then obtain x where x_in: "x \<in> X" and y_eq: "y = T x"
      by blast
    from x_in algebras have "is_algebra x"
      by simp
    hence "T x <= x"
      unfolding is_algebra_def by simp
    moreover from x_in have "x <= Sup X"
      by (rule Sup_upper)
    ultimately have "T x <= Sup X"
      by (rule order_trans)
    thus "y <= Sup X"
      unfolding y_eq .
  qed
  finally show "is_algebra (Sup X)"
    unfolding is_algebra_def by simp
qed

end

end
