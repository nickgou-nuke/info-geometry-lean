theory GNS_CBO_Fresh
  imports
    "Gelfand_Naimark_Segal.Gelfand_Naimark_Segal"
    "Complex_Bounded_Operators.Complex_Bounded_Linear_Function"
begin

text ‹
  Fresh corollary layer for the AFP entries
  @{session Complex_Bounded_Operators} and @{session Gelfand_Naimark_Segal},
  guided by the operator interface described in arXiv:2512.05878.

  This file does not redefine the GNS construction.  It records a small,
  source-traceable theorem chain showing that the GNS action is a concrete
  bounded-operator *-representation.  The heavy facts are the AFP theorem
  @{thm GNS_construction} and the bounded-operator constants/notation from
  @{theory Complex_Bounded_Operators.Complex_Bounded_Linear_Function}.
›

unbundle cblinfun_syntax

lemma gns_vector_state_recovers_state:
  fixes u :: "'a::cstar_state"
  shows "Ω ∙⇩C (π⇩ω u Ω) = ω u"
  using GNS_construction by blast

lemma gns_cyclic_vectors_dense:
  shows "closure {π⇩ω u Ω | u :: 'a::cstar_state. True} = UNIV"
  using GNS_construction by blast

lemma gns_rep_add:
  fixes a b :: "'a::cstar_state"
  shows "π⇩ω (a + b) = π⇩ω a + π⇩ω b"
  using GNS_construction by blast

lemma gns_rep_mult:
  fixes a b :: "'a::cstar_state"
  shows "π⇩ω (a * b) = cblinfun_compose (π⇩ω a) (π⇩ω b)"
  using GNS_construction by blast

lemma gns_rep_scale:
  fixes c :: complex and a :: "'a::cstar_state"
  shows "π⇩ω (c *⇩C a) = c *⇩C π⇩ω a"
  using GNS_construction by blast

lemma gns_rep_one:
  shows "π⇩ω (1 :: 'a::cstar_state) = id_cblinfun"
  using GNS_construction by blast

lemma gns_rep_involution:
  fixes a :: "'a::cstar_state"
  shows "π⇩ω (involution a) = adj (π⇩ω a)"
  using GNS_construction by blast

lemma gns_self_adjoint_element_gives_self_adjoint_operator:
  fixes a :: "'a::cstar_state"
  assumes "involution a = a"
  shows "adj (π⇩ω a) = π⇩ω a"
  using assms gns_rep_involution by metis

lemma gns_product_state_as_cyclic_matrix_coefficient:
  fixes a b :: "'a::cstar_state"
  shows "Ω ∙⇩C (π⇩ω (a * b) Ω) = ω (a * b)"
  using gns_vector_state_recovers_state by blast

lemma gns_square_is_operator_square:
  fixes a :: "'a::cstar_state"
  shows "π⇩ω (a * a) = cblinfun_compose (π⇩ω a) (π⇩ω a)"
  using gns_rep_mult by blast

lemma gns_positive_square_is_operator_adj_times_operator:
  fixes a :: "'a::cstar_state"
  shows "π⇩ω (involution a * a) = cblinfun_compose (adj (π⇩ω a)) (π⇩ω a)"
  using gns_rep_mult gns_rep_involution by metis

lemma gns_state_on_positive_square_as_cyclic_coefficient:
  fixes a :: "'a::cstar_state"
  shows "Ω ∙⇩C (cblinfun_compose (adj (π⇩ω a)) (π⇩ω a) Ω) = ω (involution a * a)"
  using gns_positive_square_is_operator_adj_times_operator gns_vector_state_recovers_state
  by metis

unbundle no cblinfun_syntax

end
