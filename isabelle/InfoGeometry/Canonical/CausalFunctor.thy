theory CausalFunctor
  imports Main "HOL-Algebra.Ring" "HOL-Algebra.Module"
begin

text \<open>
  Spacetime events ordered by causality.
  An arrow A \<longrightarrow> B exists if and only if A \<le> B causally.
\<close>

class causal_spacetime = order

text \<open>
  Two events are spacelike separated if they have no causal relationship.
\<close>
definition spacelike_separated :: "'a::causal_spacetime \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<napprox>" 50) where
  "x \<napprox> y \<equiv> \<not> (x \<le> y) \<and> \<not> (y \<le> x)"

text \<open>
  A Causal Functor maps the causal spacetime poset into the category of Algebras/Rings.
  Here we model the mapping abstractly as yielding a ring for each spacetime point, 
  with bonding maps (homomorphisms) preserving the causal order.
\<close>

locale causal_functor =
  fixes F_obj :: "'a::causal_spacetime \<Rightarrow> 'r ring"
  fixes F_map :: "'a \<Rightarrow> 'a \<Rightarrow> ('r \<Rightarrow> 'r)"
  assumes functor_id: "F_map A A x = x"
  assumes functor_comp: "A \<le> B \<Longrightarrow> B \<le> C \<Longrightarrow> F_map A C x = F_map B C (F_map A B x)"
  assumes is_ring_hom: "A \<le> B \<Longrightarrow> F_map A B \<in> ring_hom (F_obj A) (F_obj B)"

text \<open>
  Einstein Causality (Haag-Kastler Locality).
  Observables at spacelike separated events commute in the universal colimit.
\<close>

locale einstein_causality = causal_functor +
  fixes colimit_map :: "'a::causal_spacetime \<Rightarrow> ('r \<Rightarrow> 'r)"
  fixes colimit_ring :: "'r ring"
  assumes commute_of_spacelike:
    "A \<napprox> B \<Longrightarrow> x \<in> carrier (F_obj A) \<Longrightarrow> y \<in> carrier (F_obj B) \<Longrightarrow>
     (colimit_map A x) \<otimes>\<^bsub>colimit_ring\<^esub> (colimit_map B y) = (colimit_map B y) \<otimes>\<^bsub>colimit_ring\<^esub> (colimit_map A x)"

end
