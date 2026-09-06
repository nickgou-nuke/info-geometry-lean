/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.EpistemologicalOuroborosKMS

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.EpistemologicalOuroborosKMS

/-- Canonical projection capstone for Epistemological Ouroboros KMS module. -/
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
    (β - 1 = 0) :=
  grand_ouroboros_synthesis d delta gamma n m β hd hdelta hd_gamma hdelta_gamma hβ

end InfoGeometry.Canonical
