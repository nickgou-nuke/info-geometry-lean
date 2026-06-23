theory ModularEvolution
  imports CausalFunctor
begin

locale modular_evolution = einstein_causality +
  fixes sigma :: "real \<Rightarrow> 'r \<Rightarrow> 'r"
  assumes colimit_map_carrier:
    "\<And>A x. x \<in> carrier (F_obj A) \<Longrightarrow> colimit_map A x \<in> carrier colimit_ring"
  assumes sigma_hom: "\<And>t. sigma t \<in> ring_hom colimit_ring colimit_ring"
begin

theorem modular_evolution_preserves_commutativity:
  assumes "A \<napprox> B"
      and "x \<in> carrier (F_obj A)"
      and "y \<in> carrier (F_obj B)"
  shows "sigma t (colimit_map A x) \<otimes>\<^bsub>colimit_ring\<^esub> sigma t (colimit_map B y) =
         sigma t (colimit_map B y) \<otimes>\<^bsub>colimit_ring\<^esub> sigma t (colimit_map A x)"
  by (metis (full_types) assms colimit_map_carrier
      einstein_causality.commute_of_spacelike
      einstein_causality_axioms ring_hom_mult sigma_hom)

end
end
