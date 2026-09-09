import InfoGeometry.Spectral.SelbergRiemannTrace

namespace InfoGeometry.Canonical.SelbergRiemannTraceCapstone

open InfoGeometry.Spectral.SelbergRiemannTrace

/-- Canonical packaging of the proved Selberg--Riemann trace identities. -/
theorem capstone_selberg_riemann_trace_synthesis
    (p γ : ℝ) (k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (0 < primitiveGeodesicLength p) ∧
    (0 < selbergHyperbolicWeight p k) ∧
    (|spectralHarmonicTerm γ p| ≤ 1) ∧
    (spectralHarmonicTerm (-γ) p = spectralHarmonicTerm γ p) := by
  exact ⟨primitive_geodesic_length_pos p hp,
    selberg_hyperbolic_weight_pos p k hp hk,
    spectral_harmonic_bounded γ p,
    spectral_harmonic_even γ p⟩

end InfoGeometry.Canonical.SelbergRiemannTraceCapstone
