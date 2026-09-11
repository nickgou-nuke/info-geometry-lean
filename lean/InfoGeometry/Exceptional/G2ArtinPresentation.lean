/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.GroupTheory.PresentedGroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.QuotientGroup.Defs
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

def sigmaZero : ArtinG2 := PresentedGroup.of 0

def sigmaOne : ArtinG2 := PresentedGroup.of 1

theorem artin_relation :
    sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne =
      sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  simp [relations, relation]

theorem artin_relation_pow_three :
    (sigmaZero * sigmaOne) ^ 3 = (sigmaOne * sigmaZero) ^ 3 := by
  simpa [pow_succ, pow_two, mul_assoc] using artin_relation

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

@[simp] theorem coordinateAction_of (i : Generator) :
    coordinateAction (PresentedGroup.of i) = simpleReflections i := by
  exact PresentedGroup.toGroup.of (fun r hr => by
    have hr' : r = relation := by
      simpa [relations] using hr
    rw [hr']
    exact simpleReflections_relation)

@[simp] theorem coordinateAction_sigma_zero :
    coordinateAction (PresentedGroup.of (0 : Generator)) = s1Root := by
  simp [simpleReflections]

@[simp] theorem coordinateAction_sigma_one :
    coordinateAction (PresentedGroup.of (1 : Generator)) = s2Root := by
  simp [simpleReflections]

@[simp] theorem coordinateAction_sigmaZero :
    coordinateAction sigmaZero = s1Root := by
  simp [sigmaZero, simpleReflections]

@[simp] theorem coordinateAction_sigmaOne :
    coordinateAction sigmaOne = s2Root := by
  simp [sigmaOne, simpleReflections]

/-! The Artin presentation is symmetric in its two generators. -/

def generatorSwap : Generator → ArtinG2
  | 0 => sigmaOne
  | 1 => sigmaZero

theorem generatorSwap_relation :
    FreeGroup.lift generatorSwap relation = 1 := by
  simp only [relation, map_mul, map_inv, FreeGroup.lift_apply_of,
    generatorSwap, sigmaZero, sigmaOne]
  apply mul_inv_eq_one.mpr
  simpa [sigmaZero, sigmaOne] using artin_relation.symm

noncomputable def artinGeneratorSwap : ArtinG2 →* ArtinG2 :=
  PresentedGroup.toGroup (f := generatorSwap) (rels := relations) (by
    intro r hr
    have hr' : r = relation := by
      simpa [relations] using hr
    rw [hr']
    exact generatorSwap_relation)

@[simp] theorem artinGeneratorSwap_sigmaZero :
    artinGeneratorSwap sigmaZero = sigmaOne := by
  change PresentedGroup.toGroup (f := generatorSwap) (rels := relations) _
      (PresentedGroup.of 0) = sigmaOne
  rw [PresentedGroup.toGroup.of]
  rfl

@[simp] theorem artinGeneratorSwap_sigmaOne :
    artinGeneratorSwap sigmaOne = sigmaZero := by
  change PresentedGroup.toGroup (f := generatorSwap) (rels := relations) _
      (PresentedGroup.of 1) = sigmaZero
  rw [PresentedGroup.toGroup.of]
  rfl

theorem artinGeneratorSwap_involutive :
    artinGeneratorSwap.comp artinGeneratorSwap = MonoidHom.id ArtinG2 := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · change artinGeneratorSwap sigmaOne = sigmaZero
    exact artinGeneratorSwap_sigmaOne
  · change artinGeneratorSwap sigmaZero = sigmaOne
    exact artinGeneratorSwap_sigmaZero

def garsideWord : FreeGroup Generator :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
    FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1

def garside : ArtinG2 :=
  PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 0 *
    PresentedGroup.of 1 * PresentedGroup.of 0 * PresentedGroup.of 1

theorem garside_eq_reverse :
    garside =
      PresentedGroup.of 1 * PresentedGroup.of 0 * PresentedGroup.of 1 *
        PresentedGroup.of 0 * PresentedGroup.of 1 * PresentedGroup.of 0 := by
  simpa [garside, sigmaZero, sigmaOne] using artin_relation

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

/-! The Coxeter involution kernel is the normal closure of the two square
    relators.  The Artin generator swap preserves it. -/

def involutionKernel : Subgroup ArtinG2 :=
  Subgroup.normalClosure ({sigmaZero ^ 2, sigmaOne ^ 2} : Set ArtinG2)

instance : involutionKernel.Normal := by
  unfold involutionKernel
  infer_instance

theorem artinGeneratorSwap_mem_involutionKernel {g : ArtinG2}
    (hg : g ∈ involutionKernel) :
    artinGeneratorSwap g ∈ involutionKernel := by
  letI : involutionKernel.Normal := by
    dsimp [involutionKernel]
    infer_instance
  letI : (involutionKernel.comap artinGeneratorSwap).Normal :=
    Subgroup.Normal.comap (H := involutionKernel) (f := artinGeneratorSwap) inferInstance
  have hsubset :
      ({sigmaZero ^ 2, sigmaOne ^ 2} : Set ArtinG2) ⊆
        involutionKernel.comap artinGeneratorSwap := by
    intro x hx
    rcases hx with rfl | rfl
    · change artinGeneratorSwap (sigmaZero ^ 2) ∈ involutionKernel
      rw [map_pow, artinGeneratorSwap_sigmaZero]
      exact Subgroup.subset_normalClosure (by simp)
    · change artinGeneratorSwap (sigmaOne ^ 2) ∈ involutionKernel
      rw [map_pow, artinGeneratorSwap_sigmaOne]
      exact Subgroup.subset_normalClosure (by simp)
  have hle : involutionKernel ≤ involutionKernel.comap artinGeneratorSwap := by
    exact Subgroup.normalClosure_le_normal hsubset
  exact hle hg

abbrev WeylQuotient := ArtinG2 ⧸ involutionKernel

def artinQuotientMap : ArtinG2 →* WeylQuotient :=
  QuotientGroup.mk' involutionKernel

theorem artinGeneratorSwap_quotient_kernel_le :
    involutionKernel ≤ (artinQuotientMap.comp artinGeneratorSwap).ker := by
  intro g hg
  change artinQuotientMap (artinGeneratorSwap g) = 1
  exact (QuotientGroup.eq_one_iff _).2
    (artinGeneratorSwap_mem_involutionKernel hg)

def descendedArtinGeneratorSwap : WeylQuotient →* WeylQuotient :=
  QuotientGroup.lift involutionKernel
    (artinQuotientMap.comp artinGeneratorSwap)
    artinGeneratorSwap_quotient_kernel_le

@[simp] theorem descendedArtinGeneratorSwap_mk (g : ArtinG2) :
    descendedArtinGeneratorSwap (artinQuotientMap g) =
      artinQuotientMap (artinGeneratorSwap g) := by
  exact QuotientGroup.lift_mk' _ _ _

theorem artinQuotientMap_swap_commutes (g : ArtinG2) :
    artinQuotientMap (artinGeneratorSwap g) =
      descendedArtinGeneratorSwap (artinQuotientMap g) := by
  symm
  exact descendedArtinGeneratorSwap_mk g

theorem descendedArtinGeneratorSwap_involutive :
    descendedArtinGeneratorSwap.comp descendedArtinGeneratorSwap =
      MonoidHom.id WeylQuotient := by
  apply MonoidHom.ext
  intro w
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective involutionKernel w
  simp only [MonoidHom.coe_comp]
  change descendedArtinGeneratorSwap
      (descendedArtinGeneratorSwap (artinQuotientMap g)) =
    artinQuotientMap g
  rw [descendedArtinGeneratorSwap_mk, descendedArtinGeneratorSwap_mk]
  have hswap : artinGeneratorSwap (artinGeneratorSwap g) = g := by
    have h := DFunLike.congr_fun artinGeneratorSwap_involutive g
    simpa [MonoidHom.coe_comp] using h
  exact congrArg artinQuotientMap hswap

end
end InfoGeometry.Exceptional.G2ArtinPresentation
