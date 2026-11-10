/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearQuantumNumberPacket
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearAngularMomentum

/-!
# Nuclear Shell Model

This module formalizes the nuclear shell model:

1. **Shell orbitals**: Each orbital is labeled by `(n, l, j, m_j)` where:
   - `n` = principal quantum number
   - `l` = orbital angular momentum
   - `j = l ± 1/2` = total angular momentum
   - `m_j` = magnetic quantum number, `-j ≤ m_j ≤ j`

2. **Shell capacity**: A shell with angular momentum `j` can hold `2j + 1` nucleons.

3. **Seniority**: The number of unpaired nucleons in a shell. Pairing favors
   `seniority = 0` (all nucleons paired).

4. **Shell closures**: Magic numbers occur when shells are completely filled.

All statements are finite-dimensional and proven constructively in Lean 4 with
no `sorry`s.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearShellModel

open InfoGeometry.Physics.NuclearQuantumNumberPacket

variable {ι : Type*} [DecidableEq ι]

variable {𝒦 : Type*} [Field 𝒦] [CharZero 𝒦]

-- -----------------------------------------------------------------------------
-- SECTION 1: Shell orbitals
-- -----------------------------------------------------------------------------

/-- A single-particle shell orbital labeled by `(n, l, j, m_j)`. -/
structure ShellOrbital where
  n : ℕ                      -- principal quantum number
  l : ℕ                      -- orbital angular momentum
  j : ℕ                      -- total angular momentum (2j stored as integer)
  m : ℤ                      -- magnetic quantum number (-j ≤ m ≤ j)

/-- Validity condition: `-j ≤ m ≤ j`. -/
def valid_orbital (o : ShellOrbital) : Prop :=
  (o.m : ℤ) ≥ -(o.j : ℤ) ∧ (o.m : ℤ) ≤ (o.j : ℤ)

/-- Shell capacity: a shell with angular momentum `j` can hold `2j + 1` nucleons. -/
def shell_capacity (j : ℕ) : ℕ := 2 * j + 1

/-- The degeneracy of shell `j` equals `2j + 1`. -/
theorem shell_capacity_pos (j : ℕ) : shell_capacity j > 0 := by
  exact Nat.zero_lt_succ (2 * j)

-- -----------------------------------------------------------------------------
-- SECTION 2: Seniority
-- -----------------------------------------------------------------------------

/-- Seniority `v` = number of unpaired nucleons in a shell. -/
def seniority (n_occ : ℕ) (cap : ℕ) : ℕ :=
  if n_occ ≤ cap / 2 then n_occ else cap - n_occ

/-- Seniority is bounded by the shell capacity. -/
theorem seniority_le_cap (n_occ : ℕ) (cap : ℕ) : seniority n_occ cap ≤ cap := by
  unfold seniority
  split_ifs with h
  · omega
  · exact Nat.sub_le cap n_occ

-- -----------------------------------------------------------------------------
-- SECTION 3: Shell closures (magic numbers)
-- -----------------------------------------------------------------------------

/-- A shell is closed (filled) when occupation equals capacity. -/
def is_closed (n_occ : ℕ) (cap : ℕ) : Prop :=
  n_occ = cap

/-- A fully occupied shell has zero seniority: all particles are paired. -/
theorem seniority_full_shell_zero (cap : ℕ) : seniority cap cap = 0 := by
  unfold seniority
  by_cases h : cap ≤ cap / 2
  · have hcap : cap = 0 := by omega
    simp [hcap]
  · simp [h]

/-- A closed shell, expressed through `is_closed`, has zero seniority. -/
theorem seniority_zero_of_closed (n_occ cap : ℕ) (h : is_closed n_occ cap) :
    seniority n_occ cap = 0 := by
  change n_occ = cap at h
  rw [h]
  exact seniority_full_shell_zero cap

end InfoGeometry.Physics.NuclearShellModel
