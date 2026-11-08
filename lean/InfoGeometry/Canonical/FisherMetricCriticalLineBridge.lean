import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.HardyZRealizationBridge

/-!
# Supplied One-Dimensional Fisher Datum

This module formalizes only consequences of a supplied positive even scalar
function. It does not derive the function from `xi`, a likelihood, a Hessian,
or a gradient flow.

The proved consequences are:
1. **The 1D Information Fisher Metric datum**:
   $$g_F : \mathbb R \to \mathbb R$$
   is supplied as a positive even metric component.  This file does not
   assert a second-derivative identity.
2. **Positivity of the supplied metric component**:
   $$g_F(t) > 0 \quad (\forall t \notin \operatorname{ZeroSet})$$
3. No logarithmic-potential, integral-distance, gradient-flow, or
   transverse-confinement theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.FisherMetric

open Complex
open InfoGeometry.Canonical.HardyZ

/-- Datum of a Riemannian Information-Geometric Fisher Structure along the critical line -/
structure CriticalFisherDatum where
  /-- Potential function Φ : ℝ → ℝ -/
  Phi : ℝ → ℝ
  /-- Fisher metric component g_F : ℝ → ℝ -/
  g_F : ℝ → ℝ
  /-- Strictly positive Fisher metric away from singular zeros -/
  h_g_pos : ∀ t : ℝ, 0 < g_F t
  /-- Even parity of the potential Φ(-t) = Φ(t) -/
  h_Phi_even : ∀ t : ℝ, Phi (-t) = Phi t
  /-- Even parity of the Fisher metric g_F(-t) = g_F(t) -/
  h_g_even : ∀ t : ℝ, g_F (-t) = g_F t

/-- 🏆 THEOREM 1: The Fisher Metric is Non-Degenerate (Invertible) -/
theorem fisher_metric_ne_zero (D : CriticalFisherDatum) (t : ℝ) :
    D.g_F t ≠ 0 := by
  exact ne_of_gt (D.h_g_pos t)

/-- 🏆 THEOREM 2: The Inverse Fisher Metric (Information Covariance) is Strictly Positive -/
theorem fisher_inverse_pos (D : CriticalFisherDatum) (t : ℝ) :
    0 < (D.g_F t)⁻¹ := by
  exact inv_pos.mpr (D.h_g_pos t)

/-- 🏆 THEOREM 3: Even Parity of the Inverse Fisher Metric -/
theorem fisher_inverse_even (D : CriticalFisherDatum) (t : ℝ) :
    (D.g_F (-t))⁻¹ = (D.g_F t)⁻¹ := by
  rw [D.h_g_even t]

/-- 🏆 THEOREM 4: Strictly Monotonic Information Velocity:
    The Riemannian speed element ds = sqrt(g_F(t)) dt is strictly positive. -/
theorem fisher_speed_pos (D : CriticalFisherDatum) (t : ℝ) :
    0 < Real.sqrt (D.g_F t) := by
  exact Real.sqrt_pos.mpr (D.h_g_pos t)

end InfoGeometry.Canonical.FisherMetric
