/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.UHFColimitCStarCompletion
import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

/-!
# Normalized tracial state on the finite UHF stages

Genuine, matrix-representation-free-at-the-interface core extracted from the
placeholder-bearing `UHFCantorSpectralTriple` / `FirthWightmanGNS` stash lanes.
Those stash files left the state axioms as `by sorry`; here the same facts are
**proved** by descending to the already-verified normalized matrix trace owner
`CuntzMatrixTowerInstantiation`, so no proof hole is introduced.

Scope: the finite stages `UHFStage n = M_{2^n}(ℂ)` only.  No completed Hilbert
space, unbounded Dirac operator, or Wightman axiom is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFTracialStateCore

open InfoGeometry.Algebra.UHFColimitCStarCompletion
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

variable {n : ℕ}

/-- The normalized trace `ωₙ(A) = 2⁻ⁿ Tr(A)` on the finite UHF stage. -/
def uhfTracialState (n : ℕ) (A : UHFStage n) : ℂ :=
  matrixTraceState n A

/-- The normalized trace is positive on `A* A`. -/
theorem uhfTracialState_nonneg (A : UHFStage n) :
    0 ≤ (uhfTracialState n (star A * A)).re := by
  exact matrixTraceState_nonneg n A

/-- The normalized trace is unital. -/
theorem uhfTracialState_one :
    uhfTracialState n (1 : UHFStage n) = 1 := by
  exact matrixTraceState_one n

/-- The normalized trace is tracial. -/
theorem uhfTracialState_mul_comm (A B : UHFStage n) :
    uhfTracialState n (A * B) = uhfTracialState n (B * A) := by
  exact matrixTraceState_mul_comm n A B

/-- The normalized trace is real-symmetric: `ω(B* A) = ω(A* B)`. -/
theorem uhfTracialState_symmetric (A B : UHFStage n) :
    (uhfTracialState n (star B * A)).re =
      (uhfTracialState n (star A * B)).re := by
  unfold uhfTracialState
  have h := matrixTraceState_star n (star A * B)
  rw [star_mul, star_star] at h
  rw [← h]
  exact Complex.conj_re _

end InfoGeometry.Canonical.UHFTracialStateCore
