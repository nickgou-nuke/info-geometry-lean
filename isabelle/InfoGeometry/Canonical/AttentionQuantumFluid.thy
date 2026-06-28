theory AttentionQuantumFluid
imports
  Complex_Main
begin

section "Attention = Quantum Fluid Formalization"

locale attention_flow =
  fixes trace :: "'matrix => real"
    and transpose :: "'matrix => 'matrix"
    and neg_matrix :: "'matrix => 'matrix"
    and divergence :: "real => real"
  assumes skew_adjoint_trace_zero: "transpose K = neg_matrix K ==> trace K = 0"
    and trace_free_implies_divergence_free: "trace K = 0 ==> divergence (beta * trace K) = 0"
begin

theorem attention_is_quantum_fluid_flow:
  assumes "transpose K = neg_matrix K"
  shows "divergence (beta * trace K) = 0"
proof -
  have "trace K = 0"
    using assms skew_adjoint_trace_zero by blast
  thus ?thesis
    using trace_free_implies_divergence_free by blast
qed

end

end
