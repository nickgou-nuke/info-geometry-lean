/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.RHProofClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Conditional spectral closure

The upstream absolute-closure theorem referred to an owner declaration that
is no longer present.  This capstone records the current conditional theorem
without promoting it to a proof of the Riemann hypothesis.
-/

namespace InfoGeometry.Canonical.RHProofClosureCapstone

open InfoGeometry.Quantum.RHProofClosure

theorem capstone_spectral_confinement
    (sigma p : ℝ) (hp : 2 ≤ p)
    (h_unitary : spectralScalingFactor sigma p = 1) :
    sigma = 1 / 2 ∧ spectralCompletenessCondition true := by
  exact ⟨spectral_confinement_sigma_half sigma p hp h_unitary, rfl⟩

end InfoGeometry.Canonical.RHProofClosureCapstone
