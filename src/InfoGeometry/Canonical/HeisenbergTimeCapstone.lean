/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectral.HeisenbergTime
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Spectral Heisenberg Time Scaling Identities

This module establishes the logarithmic scale identities for the spectral
Heisenberg time $t_H(E) = 2\pi \bar{\rho}(E) = \log(E / 2\pi)$.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Spectral.HeisenbergTime`: `meanLevelDensity`, `heisenbergTime`,
    `heisenberg_time_log_scale`.
- BUCKET 2 (Deconfabulation):
  * Replaced the single pass-through theorem with an explicit algebraic cancellation
    derivation and proved threshold vanishing and multiplicative energy-scaling shift laws.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `capstone_heisenberg_time_synthesis`: $t_H(E) = \log(E / (2\pi))$.
  * `heisenbergTime_two_pi`: at the threshold scale $E = 2\pi$, $t_H(2\pi) = 0$.
  * `heisenbergTime_scale_mul`: for $c \neq 0$ and $E \neq 0$,
    $t_H(c E) = \log c + t_H(E)$.
-/

namespace InfoGeometry.Canonical.HeisenbergTimeCapstone

open InfoGeometry.Spectral.HeisenbergTime

/-- The spectral Heisenberg time $t_H(E) = 2\pi \bar{\rho}(E)$ reduces to
$\log(E / (2\pi))$ by cancellation of the $2\pi$ spectral prefactor. -/
theorem capstone_heisenberg_time_synthesis (E : ℝ) :
    heisenbergTime E = Real.log (E / (2 * Real.pi)) := by
  unfold heisenbergTime meanLevelDensity
  have hpi : 2 * Real.pi ≠ 0 := by linarith [Real.pi_pos]
  calc 2 * Real.pi * ((1 / (2 * Real.pi)) * Real.log (E / (2 * Real.pi)))
    _ = (2 * Real.pi * (1 / (2 * Real.pi))) * Real.log (E / (2 * Real.pi)) := by ring
    _ = 1 * Real.log (E / (2 * Real.pi)) := by rw [mul_one_div_cancel hpi]
    _ = Real.log (E / (2 * Real.pi)) := by ring

/-- At the fundamental $2\pi$ spectral threshold $E = 2\pi$, the Heisenberg time vanishes. -/
theorem heisenbergTime_two_pi :
    heisenbergTime (2 * Real.pi) = 0 := by
  rw [capstone_heisenberg_time_synthesis]
  have hpi : 2 * Real.pi ≠ 0 := by linarith [Real.pi_pos]
  rw [div_self hpi, Real.log_one]

/-- Multiplicative rescaling of the energy $E \mapsto c E$ shifts the spectral
Heisenberg time additively by $\log c$. -/
theorem heisenbergTime_scale_mul (c E : ℝ) (hc : c ≠ 0) (hE : E ≠ 0) :
    heisenbergTime (c * E) = Real.log c + heisenbergTime E := by
  rw [capstone_heisenberg_time_synthesis (c * E), capstone_heisenberg_time_synthesis E]
  have hpi : 2 * Real.pi ≠ 0 := by linarith [Real.pi_pos]
  have hdiv : c * E / (2 * Real.pi) = c * (E / (2 * Real.pi)) := by ring
  have hEdiv : E / (2 * Real.pi) ≠ 0 := div_ne_zero hE hpi
  rw [hdiv, Real.log_mul hc hEdiv]

end InfoGeometry.Canonical.HeisenbergTimeCapstone
