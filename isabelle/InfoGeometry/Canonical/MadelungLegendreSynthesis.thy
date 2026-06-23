theory MadelungLegendreSynthesis
  imports Complex_Main
begin

locale legendre_model =
  fixes fenchelGap :: "real => real => real"
    and grad :: "real => real"
  assumes fenchelGap_eq_zero: "fenchelGap theta eta = 0 \<longleftrightarrow> eta = grad theta"
begin

lemma fenchelGap_eq_zero_iff_contact:
  shows "fenchelGap theta eta = 0 \<longleftrightarrow> eta = grad theta"
  using fenchelGap_eq_zero by simp

end

locale fluid_velocity_context =
  fixes collapseToBaseVelocity :: "'a => 'b"
    and trace :: "'b => real"
    and smul_a :: "real => 'a => 'a" (infixl "*a" 70)
    and smul_b :: "real => 'b => 'b" (infixl "*b" 70)
  assumes collapse_linear: "collapseToBaseVelocity (beta *a K) = beta *b collapseToBaseVelocity K"
      and trace_linear: "trace (beta *b V) = beta * trace V"
begin

lemma trace_madelung_velocity_eq:
  shows "trace (collapseToBaseVelocity (beta *a K)) = beta * trace (collapseToBaseVelocity K)"
  by (simp add: collapse_linear trace_linear)

end
end
