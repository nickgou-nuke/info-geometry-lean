import InfoGeometry.Quantum.BaxterQQWronskian

namespace InfoGeometry.Canonical.BaxterQQWronskianCapstone

open InfoGeometry.Quantum.BaxterQQWronskian

theorem capstone_quantum_wronskian_synthesis (Γ u η : ℝ) :
    (baxterQPos Γ u * baxterQNeg Γ u = 1) ∧
    (quantumWronskian Γ u η = wronskianConstant Γ η) ∧
    (HasDerivAt (fun x : ℝ => wronskianConstant Γ η) 0 u) :=
  grand_quantum_wronskian_synthesis Γ u η

end InfoGeometry.Canonical.BaxterQQWronskianCapstone
