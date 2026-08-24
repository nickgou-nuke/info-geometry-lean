/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.GroupTheory.PresentedGroup
import InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Algebra.Zorn.G2LongestElementBridge
import InfoGeometry.Algebra.Zorn.G2ReducedWords

/-!
# The `I₂(6)` Artin presentation for the existing `G₂` Weyl action

The source here is the two-generator Artin group with relation
`(st)^3 = (ts)^3`, not the ordinary `B₃` presentation.  Its target is the
already-owned coordinate-root permutation action; the finite normal-form
readback is supplied by `G2LongestElementBridge`.

This file does not introduce a second Weyl carrier, a topological fibration,
or a physical CPT/Tomita interpretation.
-/

namespace InfoGeometry.Exceptional.G2ArtinPresentation

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
open InfoGeometry.Algebra.Zorn.G2LongestElementBridge
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2SignedRootReflections

noncomputable section

abbrev Generator := Fin 2

def relation : FreeGroup Generator :=
  (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
      FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1) *
    (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1 *
      FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0)⁻¹

def relations : Set (FreeGroup Generator) := {relation}

abbrev ArtinG2 := PresentedGroup relations

def simpleReflections : Generator → Equiv.Perm G2CoordinateRoot
  | 0 => s1Root
  | 1 => s2Root

theorem simpleReflections_relation :
    FreeGroup.lift simpleReflections relation = 1 := by
  simp only [relation, map_mul, map_inv, FreeGroup.lift_apply_of]
  apply Equiv.ext
  intro x
  have hEq : coordinateWordAction [true, false, true, false, true, false] =
      coordinateWordAction [false, true, false, true, false, true] := by
    apply Equiv.ext
    intro y
    obtain ⟨r, rfl⟩ := signedRootCoordinate_bijective.surjective y
    have hleft := coordinateWordAction_apply_signed
      [true, false, true, false, true, false] r
    have hright := coordinateWordAction_apply_signed
      [false, true, false, true, false, true] r
    have hwords :
        InfoGeometry.Algebra.Zorn.G2SignedRootReflections.simpleWordAction
            [true, false, true, false, true, false] r =
          InfoGeometry.Algebra.Zorn.G2SignedRootReflections.simpleWordAction
            [false, true, false, true, false, true] r := by
      revert r
      native_decide
    rw [hwords] at hleft
    exact hleft.trans hright.symm
  have hEq' :
      simpleReflections 0 * simpleReflections 1 * simpleReflections 0 *
          simpleReflections 1 * simpleReflections 0 * simpleReflections 1 =
        simpleReflections 1 * simpleReflections 0 * simpleReflections 1 *
          simpleReflections 0 * simpleReflections 1 * simpleReflections 0 := by
    simpa [Equiv.Perm.mul_def, simpleReflections, coordinateWordAction] using hEq.symm
  rw [hEq']
  simp

noncomputable def coordinateAction : ArtinG2 →* Equiv.Perm G2CoordinateRoot :=
  PresentedGroup.toGroup (fun r hr => by
    have hr' : r = relation := by
      simpa [relations] using hr
    rw [hr']
    exact simpleReflections_relation)

def garsideWord : FreeGroup Generator :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
    FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1

def garside : ArtinG2 :=
  PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 0 *
    PresentedGroup.of 1 * PresentedGroup.of 0 * PresentedGroup.of 1

theorem garsideWord_readback :
    FreeGroup.lift simpleReflections garsideWord =
      coordinateWordAction [false, true, false, true, false, true] := by
  apply Equiv.ext
  intro x
  simp only [garsideWord, map_mul, FreeGroup.lift_apply_of]
  simp [coordinateWordAction, simpleReflections, Equiv.Perm.mul_def,
    Equiv.trans_apply]

theorem garsideWord_is_longest_readback :
    coordinateAction garside =
      dihedralToPerm g2LongestNF := by
  apply Equiv.ext
  intro x
  simp only [garside, coordinateAction,
    PresentedGroup.toGroup.of, map_mul]
  have hreadback := congrArg (fun e : Equiv.Perm G2CoordinateRoot => e x)
    garsideWord_readback
  change (FreeGroup.lift simpleReflections garsideWord) x = _
  have hreadback' :
      (FreeGroup.lift simpleReflections garsideWord) x =
        (coordinateWordAction [false, true, false, true, false, true]) x := by
    simpa only using hreadback
  rw [hreadback']
  have hEq : coordinateWordAction [true, false, true, false, true, false] =
      coordinateWordAction [false, true, false, true, false, true] := by
    apply Equiv.ext
    intro y
    obtain ⟨r, rfl⟩ := signedRootCoordinate_bijective.surjective y
    have hleft := coordinateWordAction_apply_signed
      [true, false, true, false, true, false] r
    have hright := coordinateWordAction_apply_signed
      [false, true, false, true, false, true] r
    have hwords :
        simpleWordAction [true, false, true, false, true, false] r =
          simpleWordAction [false, true, false, true, false, true] r := by
      revert r
      native_decide
    rw [hwords] at hleft
    exact hleft.trans hright.symm
  rw [← hEq]
  have hword : toReducedWord g2LongestNF =
      [true, false, true, false, true, false] := by
    simpa [InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords.canonicalWeylWord]
      using g2LongestNF_word_canonical
  rw [← hword]
  rfl

end
end InfoGeometry.Exceptional.G2ArtinPresentation
