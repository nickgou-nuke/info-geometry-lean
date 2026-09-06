import InfoGeometry.Spectral.SelbergRiemannTrace

namespace InfoGeometry.Canonical.SelbergRiemannTraceCapstone

open InfoGeometry.Spectral.SelbergRiemannTrace

theorem capstone_selberg_riemann_trace_synthesis
    (p γ : ℝ) (k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (0 < primitiveGeodesicLength p) ∧
    (0 < selbergHyperbolicWeight p k) ∧
    (|spectralHarmonicTerm γ p| ≤ 1) ∧
    (spectralHarmonicTerm (-γ) p = spectralHarmonicTerm γ p) :=
  grand_selberg_riemann_trace_synthesis p γ k hp hk

end InfoGeometry.Canonical.SelbergRiemannTraceCapstone
