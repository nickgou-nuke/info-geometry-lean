import InfoGeometry.Canonical.HestenesKreinGeometricAlgebraBridge

namespace InfoGeometry.Canonical.HestenesKreinGeometricAlgebraCapstone

open InfoGeometry.Canonical.HestenesGA

theorem hestenes_krein_ga_canonical_capstone (F : FieldDerivatives2D) :
    (F.d1_u = F.d2_v ∧ F.d2_u = -F.d1_v) ∧
    (laplacian F = 0) ∧
    (0 ≤ energyDensity F) := by
  exact ⟨⟨F.h_cr1, F.h_cr2⟩, monogenic_field_is_harmonic F, energy_nonneg F⟩

end InfoGeometry.Canonical.HestenesKreinGeometricAlgebraCapstone
