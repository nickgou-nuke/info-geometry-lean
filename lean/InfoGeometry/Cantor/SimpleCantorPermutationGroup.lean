/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Cantor.CantorRandomWalk
import OAI.GroupTheory.BooneHigman.TwistedSimplicity

/-!
# A simple Cantor permutation group

The external twisted Brin--Thompson simple group acts by permutations of a
countable product of binary streams. This file transports that concrete
permutation group to the repo's binary-sequence Cantor carrier. The result is
a permutation group, not a claim that its elements are topological
homeomorphisms.
-/

noncomputable section

namespace InfoGeometry.Cantor.SimpleCantorPermutationGroup

open InfoGeometry.Cantor.CantorRandomWalk

abbrev CantorCube : Type :=
  OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.Cube ℕ

abbrev TwistedBrinGroup : Subgroup (Equiv.Perm CantorCube) :=
  OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.group.{0, 0}
    (Γ := PUnit) (X := ℕ)

/-- Flatten the two natural-number indices in the OAI Cantor cube to one
binary sequence index using Cantor pairing. -/
def cubeEquivCantorWord : CantorCube ≃ CantorWord where
  toFun z n := z (Nat.pairEquiv.symm n).1 (Nat.pairEquiv.symm n).2
  invFun w i j := w (Nat.pairEquiv (i, j))
  left_inv z := by
    funext i j
    simp
  right_inv w := by
    funext n
    exact congrArg w (Nat.pairEquiv.apply_symm_apply n)

/-- The image of the twisted Brin--Thompson group as permutations of the
repo's binary-sequence Cantor carrier. -/
def group : Subgroup (Equiv.Perm CantorWord) :=
  TwistedBrinGroup.map cubeEquivCantorWord.permCongrHom.toMonoidHom

/-- The OAI elementary bit flip at the first stream position of coordinate
`x`, transported to permutations of the repo's Cantor word carrier. -/
def transportedCubeBitFlip (x : ℕ) : Equiv.Perm CantorWord :=
  cubeEquivCantorWord.permCongrHom
    (OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.bitFlip
      (X := ℕ) x)

/-- Every transported elementary cube bit flip belongs to the local simple
Cantor permutation group. -/
theorem transportedCubeBitFlip_mem_group (x : ℕ) :
    transportedCubeBitFlip x ∈ group := by
  rw [group, Subgroup.mem_map]
  refine ⟨OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.bitFlip
    (X := ℕ) x, ?_, rfl⟩
  exact Subgroup.subset_closure
    (OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson.bitFlip_table
      (Γ := PUnit) (X := ℕ) x)

/-- The transported Cantor permutation group is simple. -/
theorem isSimpleGroup : IsSimpleGroup ↥group := by
  let e : ↥TwistedBrinGroup ≃* ↥group :=
    Subgroup.equivMapOfInjective TwistedBrinGroup
      cubeEquivCantorWord.permCongrHom.toMonoidHom
      cubeEquivCantorWord.permCongrHom.injective
  haveI : IsSimpleGroup ↥TwistedBrinGroup := by
    infer_instance
  exact e.symm.isSimpleGroup

end InfoGeometry.Cantor.SimpleCantorPermutationGroup
