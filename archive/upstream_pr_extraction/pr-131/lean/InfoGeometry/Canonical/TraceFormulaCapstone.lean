/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.TraceFormula

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.TraceFormula

/-- Canonical projection capstone for Quantum CFT Trace Formula module. -/
theorem trace_formula_canonical_capstone
    (γ t p : ℝ) (k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    (‖spectralTracePhase γ t‖ = 1) ∧
    (spectralTracePhase γ t + spectralTracePhase (-γ) t = ((2 * spectralCosineTerm γ t : ℝ) : ℂ)) ∧
    (0 < orbitalGutzwillerWeight p k) ∧
    (orbitalGutzwillerWeight p k = (Real.log p) / Real.exp (((k : ℝ) / 2) * Real.log p)) :=
  grand_cft_trace_formula_synthesis γ t p k hp hk

end InfoGeometry.Canonical
