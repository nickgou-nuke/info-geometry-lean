/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Canonical Boundary Surface for the Completed Current Heisenberg Law

This module provides the canonical boundary-facing Heisenberg commutator theorem
`boundaryCurrentHeisenberg` and its diagonal and off-diagonal specializations for
normal-ordered CAR currents `normalOrderedCurrent C m` inside a completed CAR mode
algebra `RawCARModeCompletion A`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.BosonizationConstructiveCurrent`:
    `RawCARModeCompletion`, `CCRBracketCompleted`, `normalOrderedCurrent`,
    `completedCentral`, `normalOrderedCurrent_heisenberg_from_matrixUnit`.
- BUCKET 2 (Deconfabulation):
  * All commutator identities are proved constructively from
    `normalOrderedCurrent_heisenberg_from_matrixUnit`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `boundaryCurrentHeisenberg`: general completed-current Heisenberg commutator.
  * `boundaryCurrentHeisenberg_diag`: resonance specialization `m + (-m) = 0`.
  * `boundaryCurrentHeisenberg_offDiag`: off-diagonal vanishing for `m + n ≠ 0`.
-/

namespace InfoGeometry.Canonical.BoundaryCurrentHeisenbergAPI

open InfoGeometry.Canonical.BosonizationConstructiveCurrent

section CanonicalCurrent

variable {A : Type*} [Ring A]

/-- Boundary current Heisenberg commutator law for normal-ordered CAR currents. -/
theorem boundaryCurrentHeisenberg
    (C : RawCARModeCompletion A) (m n : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) =
      if m + n = 0 then m • completedCentral C else 0 := by
  have h := normalOrderedCurrent_heisenberg_from_matrixUnit C m n
  exact h

/-- Diagonal resonance specialization `[J_m, J_{-m}] = m • completedCentral C`. -/
theorem boundaryCurrentHeisenberg_diag
    (C : RawCARModeCompletion A) (m : Int) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C (-m)) =
      m • completedCentral C := by
  rw [boundaryCurrentHeisenberg C m (-m)]
  have hm : m + -m = 0 := add_neg_cancel m
  simp only [hm, ↓reduceIte]

/-- Off-diagonal vanishing specialization `[J_m, J_n] = 0` when `m + n ≠ 0`. -/
theorem boundaryCurrentHeisenberg_offDiag
    (C : RawCARModeCompletion A) {m n : Int} (hmn : m + n ≠ 0) :
    CCRBracketCompleted C (normalOrderedCurrent C m) (normalOrderedCurrent C n) = 0 := by
  rw [boundaryCurrentHeisenberg C m n]
  simp only [hmn, ↓reduceIte]

end CanonicalCurrent

end InfoGeometry.Canonical.BoundaryCurrentHeisenbergAPI
