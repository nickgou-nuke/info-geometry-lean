/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic
import Omega.POM.FiberSpectrumPronyHankelRank
import Omega.POM.FiberSpectrumPronyHankelThresholdSharp

namespace Omega.POM

/-- The audited power-sum window length attached to an `R`-atom fiber spectrum. -/
def pom_fiber_spectrum_finite_reconstruction_sharp_window (R : ℕ) : ℕ :=
  2 * R

/-- Rank identification for the concrete finite-spectrum Hankel matrix. -/
def pom_fiber_spectrum_finite_reconstruction_sharp_rank
    (D : FiberSpectrumPronyHankelRankData) : Prop :=
  D.hankelRank = D.atomCount

/-- Paper label: `thm:pom-fiber-spectrum-finite-reconstruction-sharp`. This package proves the
finite-spectrum Hankel rank and the stated threshold-gap identities. It does not formalize an
injective reconstruction map from the first `2R` power sums to spectral data. -/
theorem paper_pom_fiber_spectrum_finite_reconstruction_sharp
    (D : FiberSpectrumPronyHankelRankData) (hR : 2 ≤ D.atomCount) :
    pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount = 2 * D.atomCount ∧
      pom_fiber_spectrum_finite_reconstruction_sharp_rank D ∧
      (∀ k : ℕ, k ≤ pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 2 →
        pomPronyHankelThresholdGap D.atomCount k = 0) ∧
      pomPronyHankelThresholdGap D.atomCount
          (pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 1) =
        Nat.factorial
          (pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount - 1) := by
  have hReconstruct := paper_pom_fiber_spectrum_prony_hankel_rank D
  have hSharp := paper_pom_fiber_spectrum_prony_hankel_threshold_sharp D.atomCount hR
  refine ⟨rfl, hReconstruct, ?_, ?_⟩
  · intro k hk
    exact hSharp.1 k (by simpa [pom_fiber_spectrum_finite_reconstruction_sharp_window] using hk)
  · simpa [pom_fiber_spectrum_finite_reconstruction_sharp_window] using hSharp.2

end Omega.POM
