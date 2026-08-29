/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Spectral.RiemannWeilTrace

namespace InfoGeometry.Canonical

open InfoGeometry.Spectral.RiemannWeilTrace

/-- 🏆 GRAND CANONICAL CAPSTONE: Riemann-Weil Trace Formula on Apollonian Cylinder -/
theorem grand_canonical_riemann_weil_trace_synthesis
    (p : ℝ) (m m₁ m₂ : ℕ) (γ τ : ℝ) (hp : 1 < p) (hm : 1 ≤ m) :
    (0 < primeOrbitWeight p m) ∧
    (‖primePhaseHolonomy p m γ‖ = 1) ∧
    (primePhaseHolonomy p (m₁ + m₂) γ =
     primePhaseHolonomy p m₁ γ * primePhaseHolonomy p m₂ γ) ∧
    (monochromaticSpectralMode (-γ) τ = monochromaticSpectralMode γ τ) ∧
    (let val_pos := (Complex.exp (Complex.I * ((Complex.I / 2) * (τ : ℂ))) +
                    Complex.exp (-Complex.I * ((Complex.I / 2) * (τ : ℂ)))) / 2
     let val_neg := (Complex.exp (Complex.I * ((-Complex.I / 2) * (τ : ℂ))) +
                    Complex.exp (-Complex.I * ((-Complex.I / 2) * (τ : ℂ)))) / 2
     (val_pos + val_neg).re = 2 * Real.cosh (τ / 2)) :=
  grand_riemann_weil_trace_synthesis p m m₁ m₂ γ τ hp hm

end InfoGeometry.Canonical
