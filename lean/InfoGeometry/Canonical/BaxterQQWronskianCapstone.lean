import InfoGeometry.Quantum.BaxterQQWronskian

namespace InfoGeometry.Canonical.BaxterQQWronskianCapstone

open InfoGeometry.Quantum.BaxterQQWronskian

theorem capstone_quantum_wronskian_synthesis (Γ u η : ℝ) :
    (baxterQPos Γ u * baxterQNeg Γ u = 1) ∧
    (quantumWronskian Γ u η = wronskianConstant Γ η) ∧
    (HasDerivAt (fun _ : ℝ => wronskianConstant Γ η) 0 u) :=
  ⟨baxter_Q_pos_mul_neg_eq_one Γ u,
   quantum_wronskian_eq_constant Γ u η,
   hasDerivAt_wronskian_zero Γ η u⟩

end InfoGeometry.Canonical.BaxterQQWronskianCapstone
