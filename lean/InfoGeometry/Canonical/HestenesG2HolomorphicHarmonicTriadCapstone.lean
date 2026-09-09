import InfoGeometry.Canonical.HestenesG2HolomorphicHarmonicTriadBridge

namespace InfoGeometry.Canonical.HestenesG2HolomorphicHarmonicTriadCapstone

open InfoGeometry.Canonical.HestenesTriad

theorem hestenes_g2_triad_canonical_capstone (F : SmoothField2D) (x : Cl2) :
    (EvenCl2.I * EvenCl2.I = -1 ∧ ∀ a b : EvenCl2, a * b = b * a) ∧
    (nabla_psi F = 0 ↔ (F.d1_u = F.d2_v ∧ F.d2_u = -F.d1_v)) ∧
    (laplacian_u F = 0 ∧ laplacian_v F = 0) ∧
    (P_L x + P_R x = x ∧ P_L (P_L x) = P_L x ∧ P_R (P_R x) = P_R x ∧
      P_L (P_R x) = 0 ∧ Cl2.I * (P_L x) * Cl2.I = P_L x ∧
      Cl2.I * (P_R x) * Cl2.I = -P_R x) ∧
    (wirtinger_dbar F = 0 ↔ nabla_psi F = 0) ∧
    (0 ≤ gradientEnergyDensity F) := by
  refine ⟨⟨EvenCl2.I_sq, EvenCl2.mul_comm⟩,
    monogenic_iff_cauchy_riemann F, ⟨monogenic_u_harmonic F, monogenic_v_harmonic F⟩, ?_,
    wirtinger_dbar_eq_zero_iff_monogenic F, gradient_energy_nonneg F⟩
  exact ⟨chiral_completeness x, P_L_idempotent x, P_R_idempotent x,
    (chiral_orthogonality x).1, (chiral_pseudoscalar_sandwich x).1,
    (chiral_pseudoscalar_sandwich x).2⟩

end InfoGeometry.Canonical.HestenesG2HolomorphicHarmonicTriadCapstone
