import InfoGeometry.Quantum.SelbergApollonianGeodesicTrace

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.SelbergApollonianGeodesicTrace

/-- Canonical packaging of the finite Selberg--Apollonian trace identities. -/
theorem selberg_apollonian_geodesic_trace_canonical_capstone
    (p q γ : ℝ) (k : ℕ) (hp : 2 ≤ p) (hq : 0 < q) (hk : 1 ≤ k) :
    (0 < primitiveGeodesicLength p) ∧
    (primitiveGeodesicLength (p * q) = primitiveGeodesicLength p + primitiveGeodesicLength q) ∧
    (0 < selbergOrbitalWeight p k) ∧
    (|spectralResonance γ p| ≤ 1) := by
  exact ⟨primitive_geodesic_length_pos p hp,
    geodesic_length_multiplicative p q (by linarith) hq,
    selberg_orbital_weight_pos p k hp hk,
    spectral_resonance_bounded γ p⟩

end InfoGeometry.Canonical
