/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Cantor.SimpleCantorPermutationGroup

/-!
# Finite mode transpositions inside the simple Cantor group

The finite Clifford/Fock symmetry permutes mode labels. A transposition of
two Cantor bit coordinates is itself a finite prefix rearrangement, hence an
element of the simple Cantor permutation group. This records the common
permutation generators without identifying the Cantor function space with
the Fock module.
-/

noncomputable section

namespace InfoGeometry.Cantor.SimpleCantorFiniteModeBridge

open InfoGeometry.Cantor.CantorRandomWalk
open InfoGeometry.Cantor.SimpleCantorPermutationGroup
open OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson

/-- The finite prefix partition that records the first bits at two stream
coordinates. -/
def twoModePartition (i j : ℕ) : Partition ℕ :=
  (Partition.bit i).allRefine (Partition.bit j)

/-- The index permutation that interchanges the two Boolean coordinates. -/
def twoModeIndexSwap (i j : ℕ) :
    Equiv.Perm ((Partition.bit i).index × (Partition.bit j).index) :=
  Equiv.prodComm (Partition.bit i).index (Partition.bit j).index

/-- Swap the two first-bit prefix classes while preserving their common tail. -/
def cubeFirstBitSwap (i j : ℕ) : Equiv.Perm (Cube ℕ) :=
  (twoModePartition i j).mapPerm (twoModePartition i j)
    (twoModeIndexSwap i j)

/-- The corresponding permutation of the repo's Cantor-word carrier. -/
def cantorFirstBitSwap (i j : ℕ) : Equiv.Perm CantorWord :=
  cubeEquivCantorWord.permCongr (cubeFirstBitSwap i j)

/-- Every finite first-bit transposition belongs to the simple Cantor
permutation group. The witness is the actual OAI finite-table group element
transported across Cantor pairing. -/
theorem cantorFirstBitSwap_mem_group (i j : ℕ) :
    cantorFirstBitSwap i j ∈ group := by
  let P := twoModePartition i j
  have hcube : cubeFirstBitSwap i j ∈ TwistedBrinGroup := by
    exact (P.permute (Γ := PUnit) (twoModeIndexSwap i j)).property
  change cantorFirstBitSwap i j ∈
    TwistedBrinGroup.map cubeEquivCantorWord.permCongrHom.toMonoidHom
  rw [Subgroup.mem_map]
  exact ⟨cubeFirstBitSwap i j, hcube, rfl⟩

end InfoGeometry.Cantor.SimpleCantorFiniteModeBridge

end
