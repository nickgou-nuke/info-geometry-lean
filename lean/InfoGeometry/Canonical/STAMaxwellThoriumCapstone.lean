import InfoGeometry.Canonical.HestenesSTA4DMaxwellDiracBridge
import InfoGeometry.Canonical.Thorium229NuclearIsomerSpinorBridge

namespace InfoGeometry.Canonical.STAMaxwellThoriumCapstone

open InfoGeometry.Canonical.SpacetimeAlgebra
open InfoGeometry.Canonical.Thorium229

theorem sta_maxwell_thorium229_canonical_capstone
    (C : EMSpacetimeConfig) (F : FieldBivector) (ψ : STASpinor)
    (S : ThoriumState) (R : SpinRotor3D) :
    (maxwell_vector_residual C = ⟨0, 0, 0, 0⟩ ∧
      maxwell_trivector_residual C = ⟨0, 0, 0, 0⟩) ∧
    (0 ≤ emEnergyDensity F) ∧
    (0 ≤ STASpinor.current_j0 ψ ∧
      (STASpinor.current_j0 ψ = 0 ↔
        ψ = ⟨0, 0, 0, 0, 0, 0, 0, 0⟩)) ∧
    (300 < beta_deltaE) ∧
    ((SpinRotor3D.mul R (SpinRotor3D.reverse R)).cos_half = 1 ∧
      (SpinRotor3D.mul R (SpinRotor3D.reverse R)).sin_half = 0) ∧
    ((R.cos_half * S.psi_g - R.sin_half * S.psi_e) ^ 2 +
      (R.sin_half * S.psi_g + R.cos_half * S.psi_e) ^ 2 = 1) := by
  exact ⟨maxwell_spacetime_satisfaction C, em_energy_density_nonneg F,
    ⟨STASpinor.current_j0_nonneg ψ, STASpinor.current_j0_zero_iff ψ⟩,
    beta_deltaE_large, SpinRotor3D.mul_reverse_unit R,
    rotor_action_preserves_norm S R⟩

end InfoGeometry.Canonical.STAMaxwellThoriumCapstone
