theory AdelicSymmetrySpectrum
  imports Complex_Main
begin

locale adelic_symmetry =
  fixes inner :: "'v ⇒ 'v ⇒ complex"
  and add :: "'v ⇒ 'v ⇒ 'v"
  and scale :: "complex ⇒ 'v ⇒ 'v"
  and D :: "'v ⇒ 'v"
  and D_dag :: "'v ⇒ 'v"
  and v :: "'v"
  and lambda :: "complex"
  assumes inner_add_right: "inner u (add x y) = inner u x + inner u y"
  and inner_scale_right: "inner u (scale c x) = c * inner u x"
  and inner_symm: "inner u y = cnj (inner y u)"
  and D_adj_prop: "inner (D_dag u) y = inner u (D y)"
  and D_identity: "add (D x) (D_dag x) = x"
  and D_eigen: "D v = scale lambda v"
  and inner_v_v_neq_0: "inner v v ≠ 0"
begin

lemma inner_scale_left: "inner (scale c x) y = cnj c * inner x y"
proof -
  have "inner (scale c x) y = cnj (inner y (scale c x))" by (simp add: inner_symm)
  also have "... = cnj (c * inner y x)" by (simp add: inner_scale_right)
  also have "... = cnj c * cnj (inner y x)" by simp
  also have "... = cnj c * inner x y" by (simp add: inner_symm)
  finally show ?thesis .
qed

lemma inner_D_dag_eigen: "inner (D_dag v) v = cnj lambda * inner v v"
proof -
  have "inner (D_dag v) v = inner v (D v)" by (simp add: D_adj_prop)
  also have "... = inner v (scale lambda v)" by (simp add: D_eigen)
  also have "... = lambda * inner v v" by (simp add: inner_scale_right)
  finally show ?thesis .
qed

lemma spectrum_real_part: "Re lambda = 1/2"
proof -
  have "inner v v = inner v (add (D v) (D_dag v))" by (simp add: D_identity)
  also have "... = inner v (D v) + inner v (D_dag v)" by (simp add: inner_add_right)
  also have "... = inner v (scale lambda v) + cnj (inner (D_dag v) v)" by (simp add: D_eigen inner_symm)
  also have "... = lambda * inner v v + cnj (cnj lambda * inner v v)" by (simp add: inner_scale_right inner_D_dag_eigen)
  also have "... = lambda * inner v v + lambda * cnj (inner v v)" by simp
  also have "... = lambda * inner v v + lambda * inner v v" using inner_symm[of v v] by simp
  also have "... = (2 * lambda) * inner v v" by (simp add: algebra_simps)
  finally have "inner v v = 2 * lambda * inner v v" .
  then have "(1 - 2 * lambda) * inner v v = 0" by (simp add: algebra_simps)
  with inner_v_v_neq_0 have "1 - 2 * lambda = 0" by simp
  then have "lambda = 1/2" by simp
  then show ?thesis by simp
qed

end
end
