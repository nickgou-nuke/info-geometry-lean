import InfoGeometry.Quantum.EpistemologicalOuroborosKMS

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.EpistemologicalOuroborosKMS

/-- Canonical packaging of the Dirac--Hodge and modular-weight identities.

The hypotheses are exactly those required by the two algebraic identities;
the KMS normalization and multiplicativity are supplied by their owner. -/
theorem epistemological_ouroboros_kms_canonical_capstone {R : Type*} [CommRing R]
    (d delta gamma : R) (n m : ℕ) (β : ℝ)
    (hd : d * d = 0) (hdelta : delta * delta = 0)
    (hd_gamma : anticommutator gamma d = 0)
    (hdelta_gamma : anticommutator gamma delta = 0)
    (hβ : β = 1) :
    ((graphDirac d delta) * (graphDirac d delta) = hodgeLaplacian d delta) ∧
    (anticommutator gamma (graphDirac d delta) = 0) ∧
    (kmsModularWeight 1 β = 1) ∧
    (kmsModularWeight (n * m) β = kmsModularWeight n β * kmsModularWeight m β) ∧
    (β - 1 = 0) := by
  exact ⟨graph_dirac_sq_eq_hodge_laplacian d delta hd hdelta,
    chiral_grading_anticommutes_dirac d delta gamma hd_gamma hdelta_gamma,
    kms_modular_weight_one β,
    kms_modular_weight_mul n m β,
    kms_critical_temperature_balance β hβ⟩

end InfoGeometry.Canonical
