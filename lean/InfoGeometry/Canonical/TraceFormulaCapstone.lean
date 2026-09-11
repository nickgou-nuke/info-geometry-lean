/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.TraceFormula
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.TraceFormula

theorem trace_formula_canonical_capstone
    (γ t p : ℝ) (k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (‖spectralTracePhase γ t‖ = 1) ∧
    (spectralTracePhase γ t + spectralTracePhase (-γ) t =
      ((2 * spectralCosineTerm γ t : ℝ) : ℂ)) ∧
    (0 < orbitalGutzwillerWeight p k) ∧
    (orbitalGutzwillerWeight p k =
      (Real.log p) / Real.exp (((k : ℝ) / 2) * Real.log p)) := by
  exact ⟨spectral_trace_phase_unitary γ t,
    spectral_pair_trace_real γ t,
    orbital_gutzwiller_weight_pos p k hp hk,
    orbital_gutzwiller_weight_div_form p k (by linarith)⟩

end InfoGeometry.Canonical
