/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.PerelmanWCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.PerelmanW

open RicciMongeAmpere
open SpectralInference

section SpinorialBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Absolute scalar-Ricci beta function, used as the nonnegative dissipation. -/
noncomputable def scalarRicciWDissipation
    (flow : ScalarRicciFlow E) (scale : ℝ) : ℝ :=
  |scalarRicciBetaFunction (E := E) flow scale|

/-- A differentiable functional following absolute scalar-Ricci dissipation is monotone. -/
theorem w_monotone_of_scalarRicci_dissipation
    (flow : ScalarRicciFlow E) (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = scalarRicciWDissipation flow s) :
    Monotone W := by
  apply monotone_of_deriv_nonneg hDiff
  intro s
  rw [hW s, scalarRicciWDissipation]
  exact abs_nonneg _

/-- If the scalar-Ricci beta function never vanishes, the dissipation is strictly positive. -/
theorem w_strictMono_of_scalarRicci_dissipation
    (flow : ScalarRicciFlow E) (W : ℝ → ℝ)
    (hW : ∀ s : ℝ, deriv W s = scalarRicciWDissipation flow s)
    (hBeta : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s ≠ 0) :
    StrictMono W := by
  apply strictMono_of_deriv_pos
  intro s
  rw [hW s, scalarRicciWDissipation]
  exact abs_pos.mpr (hBeta s)

/-- If the scalar-Ricci beta function vanishes everywhere, a differentiable `W`
following its absolute value is constant. -/
theorem w_constant_of_zero_scalarRicci_beta
    (flow : ScalarRicciFlow E) (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = scalarRicciWDissipation flow s)
    (hBeta : ∀ s : ℝ, scalarRicciBetaFunction (E := E) flow s = 0) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  refine ⟨W 0, ?_⟩
  intro s
  have hDerivZero : ∀ t : ℝ, deriv W t = 0 := by
    intro t
    rw [hW t, scalarRicciWDissipation, hBeta t]
    simp
  simpa using is_const_of_deriv_eq_zero (f := W) hDiff hDerivZero s 0

end SpinorialBridge

end InfoGeometry.Canonical.PerelmanW
