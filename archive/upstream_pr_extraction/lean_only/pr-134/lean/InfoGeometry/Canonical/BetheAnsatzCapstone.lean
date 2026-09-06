import InfoGeometry.Quantum.BetheAnsatz

namespace InfoGeometry.Canonical.BetheAnsatzCapstone

open InfoGeometry.Quantum.BetheAnsatz

theorem capstone_bethe_ansatz_synthesis
    (Γ u u_k Θ : ℝ) (I_k : ℤ) (h_quant : Γ * u_k - Θ = 2 * Real.pi * (I_k : ℝ)) :
    (‖vacuumEigenvalueA Γ u‖ = 1 ∧ ‖vacuumEigenvalueD Γ u‖ = 1) ∧
    (vacuumEigenvalueA Γ u / vacuumEigenvalueD Γ u = betheVacuumRatio Γ u) ∧
    (vacuumEigenvalueA Γ u + vacuumEigenvalueD Γ u = ((2 * Real.cos ((Γ / 2) * u) : ℝ) : ℂ)) ∧
    (betheVacuumRatio Γ u_k = betheScatteringPhase Θ ↔
     Complex.exp (Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ))) = 1) ∧
    (Complex.exp (Complex.I * (((Γ * u_k - Θ : ℝ) : ℂ))) = 1) :=
  grand_bethe_ansatz_synthesis Γ u u_k Θ I_k h_quant

end InfoGeometry.Canonical.BetheAnsatzCapstone
