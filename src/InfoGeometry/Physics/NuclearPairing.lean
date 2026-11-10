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
import InfoGeometry.Physics.NuclearQuasiparticleCARBridge

/-!
# Nuclear Pairing Theory

This module formalizes the BCS pairing mechanism for nuclear quasiparticles:

1. **Pairing Hamiltonian**: The pairing interaction
   `H_pair = -G ∑_{i,j} a†_i a†_j a_j a_i` where `G > 0` is the pairing strength.

2. **Pairing gap parameter**: `Δ = G ∑_k u_k v_k`.

All statements are finite-dimensional and proven constructively in Lean 4 with
no `sorry`s.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearPairing

open InfoGeometry.Physics.NuclearQuantumNumberPacket
open InfoGeometry.Physics.NuclearQuasiparticleCAR

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

variable (car : QuasiparticleCAR ι A)

/-- Pairing strength `G > 0` for the pairing Hamiltonian. -/
def pairing_strength : ℝ := 1

/-- Pairing strength is positive. -/
theorem pairing_strength_pos : pairing_strength > 0 := by
  norm_num [pairing_strength]

/-- Pairing Hamiltonian: H_pair = -G ∑_{i,j} a†_i a†_j a_j a_i.
   The pairing interaction scatters pairs of nucleons between time-reversed
   orbitals. -/
def pairing_hamiltonian : A :=
  -(pairing_strength : ℝ) • ∑ i : ι, ∑ j : ι,
    car.adag i * car.adag j * car.a j * car.a i

/-- Pairing gap parameter: Δ = G ∑_k u_k v_k. -/
def pairing_gap (u v : ι → ℝ) : ℝ :=
  pairing_strength * ∑ i : ι, u i * v i

end InfoGeometry.Physics.NuclearPairing