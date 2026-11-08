/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Causal Poset: Zero-Orbit Energy Arithmetic and the Type-D Mass Gap

This module synthesizes the Type-D Weyl-orbit rigidity and mass gap arithmetic
extracted from SubregularAffineCells-Lean into the unified E10/Pin(5,5)
geometry framework.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Integer level scale `N r = 2 * r + 1` and single-coordinate quadratic form
    `coordContribution r t n = N r * n^2 + 2 * t * n`.
- BUCKET 2 (Deconfabulation):
  * Every arithmetic bound (`N_pos`, `coordContribution_nonneg`, `coordContribution_exception`,
    `mass_gap_isolation`) is proved directly over `ℤ` with explicit hypothesis consumption.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `N_pos`, `coordContribution_nonneg`, `coordContribution_exception`, `mass_gap_isolation`.
-/

namespace InfoGeometry.GrandUnification.TypeDZeroOrbit

/-- Archetype I: Level Scale `N r = 2r + 1` characterizing the affine level `-1` boundary. -/
def N (r : ℤ) : ℤ := 2 * r + 1

/-- For `0 ≤ r`, the level scale `N r = 2r + 1` is strictly positive. -/
theorem N_pos {r : ℤ} (hr : 0 ≤ r) : 0 < N r := by
  dsimp [N]
  linarith [hr]

/-- Archetype II: Local Energy Functional `f_t(n) = N(r) n^2 + 2 t n`. -/
def coordContribution (r t n : ℤ) : ℤ :=
  N r * n ^ 2 + 2 * t * n

/-- Archetype III: Interior Energy Positivity.
For all coordinates inside the Weyl chamber (`0 ≤ t ≤ r` with `3 ≤ r`),
the quadratic coordinate contribution is non-negative. -/
theorem coordContribution_nonneg (r t n : ℤ) (hr : 3 ≤ r) (ht0 : 0 ≤ t) (htr : t ≤ r) :
    0 ≤ coordContribution r t n := by
  dsimp [coordContribution, N]
  obtain hn | rfl | hn := lt_trichotomy n 0
  · have hn1 : n ≤ -1 := by omega
    have hsq : -n ≤ n ^ 2 := by nlinarith [hn1]
    nlinarith [hr, ht0, htr, hsq, hn1]
  · norm_num
  · have hn1 : 1 ≤ n := by omega
    have hsq : n ≤ n ^ 2 := by nlinarith [hn1]
    nlinarith [hr, ht0, htr, hsq, hn1]

/-- Archetype IV: The Boundary Defect.
At the exceptional boundary coordinate `t = r + 1`, a defect of `-1` occurs
for the reflection jump `n = -1`. -/
theorem coordContribution_exception (r : ℤ) :
    coordContribution r (r + 1) (-1) = -1 := by
  dsimp [coordContribution, N]
  ring

/-- Archetype V: Mass Gap Isolation.
Any non-zero jump `n ≠ -1` at the boundary coordinate `t = r + 1` resolves strictly
positive (`≥ 1`), isolating the `n = -1` defect. -/
theorem mass_gap_isolation (r n : ℤ) (hr : 3 ≤ r) (hn : n ≠ -1 ∧ n ≠ 0) :
    1 ≤ coordContribution r (r + 1) n := by
  dsimp [coordContribution, N]
  have hne1 : n ≠ -1 := hn.1
  have hne0 : n ≠ 0 := hn.2
  rcases lt_trichotomy n 0 with h1 | rfl | h2
  · have hn1 : n ≤ -2 := by omega
    have hsq : -2 * n ≤ n ^ 2 := by nlinarith [hn1]
    nlinarith [hr, hsq, hn1]
  · exact False.elim (hne0 rfl)
  · have hn1 : 1 ≤ n := by omega
    have hsq : n ≤ n ^ 2 := by nlinarith [hn1]
    nlinarith [hr, hsq, hn1, hne1]

end InfoGeometry.GrandUnification.TypeDZeroOrbit
