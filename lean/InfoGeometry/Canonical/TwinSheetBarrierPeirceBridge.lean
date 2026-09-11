import InfoGeometry.Modular.SelfConcordantBarrierTriple
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Modular.TrifactorTripotentUnification

/-!
# Twin-sheet barrier readouts and Peirce spectral coordinates

This file is deliberately an aggregation bridge.  The positive sheet pair is
the primary datum; volume and chiral quantities are its Hadamard readouts.
The analytic `TwinWaveState`/`DoubledSpace` equivalence and the scalar Schur
cross-term are owned by `Quantum.TwinWaveCayleyDickson`; this file only adds
the independent barrier/Peirce readout bridge.
-/

noncomputable section

open BigOperators

namespace InfoGeometry.Canonical.TwinSheetBarrierPeirceBridge

open InfoGeometry.Modular.SelfConcordance
open InfoGeometry.Modular.TrifactorTripotentUnification

variable {ι : Type*} [Fintype ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-! ## The two sheet potentials and their Hadamard readouts -/

/-- The two positive-sheet log barriers recovered from the even/chiral pair. -/
theorem sheet_logBarrier_recovery
    (a d : PositiveState ι) :
    logBarrier a = (barrierVol a d + barrierChir a d) / 2 ∧
    logBarrier d = (barrierVol a d - barrierChir a d) / 2 := by
  constructor <;>
    dsimp [barrierVol, barrierChir] <;>
    ring

/-- The inverse Hadamard identities for arbitrary scalar sheet values. -/
theorem hadamard_inverse
    (u v : ℝ) :
    ((u + v) / 2 + (u - v) / 2 = u) ∧
    ((u + v) / 2 - (u - v) / 2 = v) := by
  constructor <;> ring

/-! ## Compatibility with the existing Peirce spectral owner -/

/-- The Peirce coefficients `(α + β, α - β, α)` are recovered from the
    volume/chiral Hadamard pair and the neutral coefficient. -/
theorem peirce_coefficients_from_sheet_readouts
    (volume chiral : ℝ) :
    let alpha := (volume + chiral) / 2
    let beta := (volume - chiral) / 2
    alpha + beta = volume ∧
      alpha - beta = chiral ∧
      alpha = (volume + chiral) / 2 := by
  dsimp
  constructor
  · ring
  constructor
  · ring
  · rfl

/-- The existing tripotent spectral theorem, with its coefficients exposed as
    the two-sheet Hadamard readouts.  No new projector or carrier is defined.
-/
theorem peirce_spectral_split_from_sheet_readouts
    (inv2 : ℝ) (h2 : (2 : ℝ) * inv2 = 1)
    (volume chiral : ℝ) (T : A) :
    let alpha := (volume + chiral) / 2
    let beta := (volume - chiral) / 2
    alpha • (1 : A) + beta • T =
      volume • projPlus inv2 T +
        chiral • projMinus inv2 T +
          alpha • projZero T := by
  dsimp
  have hsplit :=
    trifactor_surprisal_peirce_spectral_split
      inv2 h2 ((volume + chiral) / 2) ((volume - chiral) / 2) T
  have hplus :
      (volume + chiral) / 2 + (volume - chiral) / 2 = volume := by
    ring
  have hminus :
      (volume + chiral) / 2 - (volume - chiral) / 2 = chiral := by
    ring
  rw [hplus, hminus] at hsplit
  exact hsplit

end InfoGeometry.Canonical.TwinSheetBarrierPeirceBridge
