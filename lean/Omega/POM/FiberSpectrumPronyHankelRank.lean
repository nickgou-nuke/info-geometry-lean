/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Omega.POM.FiniteMomentHankelRank

namespace Omega.POM

/-- Finite rational spectral data used to form an actual moment Hankel matrix. -/
structure FiberSpectrumPronyHankelRankData where
  atomCount : ℕ
  support : Fin atomCount → ℚ
  weight : Fin atomCount → ℚ
  support_injective : Function.Injective support
  weight_ne_zero : ∀ i, weight i ≠ 0

/-- The Hankel rank computed from the record's actual finite spectral data. -/
noncomputable def FiberSpectrumPronyHankelRankData.hankelRank
    (D : FiberSpectrumPronyHankelRankData) : ℕ :=
  (finiteMomentHankel D.support D.weight).rank

/-- For finite rational support with nonzero weights, the actual moment Hankel matrix has full rank.
    thm:pom-fiber-spectrum-prony-hankel-rank -/
theorem paper_pom_fiber_spectrum_prony_hankel_rank (D : FiberSpectrumPronyHankelRankData) :
    D.hankelRank = D.atomCount := by
  simpa [FiberSpectrumPronyHankelRankData.hankelRank] using
    finiteMomentHankel_rank D.support D.weight D.support_injective D.weight_ne_zero

end Omega.POM
