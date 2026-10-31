/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Cantor.SimpleCantorPermutationGroup
import InfoGeometry.Cantor.SimpleCantorFiniteModeBridge
import InfoGeometry.Cantor.PermutationOperator
import OAI.GroupTheory.BooneHigman.Generators

/-!
# The simple Cantor permutation group as noncommutative operators

The simple Cantor permutation group acts faithfully by invertible linear
operators on real-valued functions on the Cantor cube. Its operator image is
therefore a group of units in an endomorphism algebra, with simplicity
transported through the faithful representation.
-/

noncomputable section

namespace InfoGeometry.Cantor.SimpleCantorOperatorGroup

open InfoGeometry.Cantor.SimpleCantorPermutationGroup
open InfoGeometry.Cantor.SimpleCantorFiniteModeBridge
open InfoGeometry.Cantor.CantorRandomWalk
open OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson
open InfoGeometry.Cantor.PermutationOperator

/-- The permutation operator on functions, using inverse reindexing so
operator composition agrees with permutation multiplication. -/
def operator (g : ↥group) : Module.End ℝ (CantorWord → ℝ) :=
  InfoGeometry.Cantor.PermutationOperator.operator (R := ℝ)
    (g : Equiv.Perm CantorWord)

@[simp] theorem operator_apply (g : ↥group) (f : CantorWord → ℝ)
    (x : CantorWord) : operator g f x = f (((g : Equiv.Perm CantorWord)⁻¹) x) := rfl

/-- The simple Cantor group represented in the endomorphism monoid. -/
def operatorRep : ↥group →* Module.End ℝ (CantorWord → ℝ) :=
  InfoGeometry.Cantor.PermutationOperator.operatorRep (R := ℝ) |>.comp group.subtype

/-- The represented permutation, packaged as an invertible operator. -/
def operatorUnit (g : ↥group) : (Module.End ℝ (CantorWord → ℝ))ˣ :=
  InfoGeometry.Cantor.PermutationOperator.operatorUnit (R := ℝ)
    (g : Equiv.Perm CantorWord)

/-- The operator-unit representation of the simple Cantor group. -/
def operatorUnitRep : ↥group →* (Module.End ℝ (CantorWord → ℝ))ˣ :=
  InfoGeometry.Cantor.PermutationOperator.operatorUnitRep (X := CantorWord) (R := ℝ) |>.comp
    group.subtype

/-- Function probes separate distinct Cantor permutations, so the operator
representation is faithful. -/
theorem operatorUnitRep_injective : Function.Injective operatorUnitRep := by
  exact (InfoGeometry.Cantor.PermutationOperator.operatorUnitRep_injective
    (X := CantorWord) (R := ℝ)).comp Subtype.val_injective

/-- The simple Cantor permutation group as an actual subgroup of
endomorphism units. -/
def operatorGroup : Subgroup (Module.End ℝ (CantorWord → ℝ))ˣ :=
  (⊤ : Subgroup (↥group)).map operatorUnitRep

/-- The representation with codomain restricted to its operator image. -/
def operatorRangeRep : ↥group →* ↥operatorGroup where
  toFun g := ⟨operatorUnitRep g, Subgroup.mem_map.mpr ⟨g, trivial, rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one operatorUnitRep
  map_mul' g h := by apply Subtype.ext; exact map_mul operatorUnitRep g h

/-- The operator image retains the external source's simplicity theorem. -/
theorem isSimpleGroup : IsSimpleGroup ↥operatorGroup := by
  let e : ↥group ≃* ↥operatorGroup :=
    MulEquiv.ofBijective operatorRangeRep
      ⟨fun g h hh => operatorUnitRep_injective (congrArg Subtype.val hh),
       fun u => by
         obtain ⟨g, _, hg⟩ := Subgroup.mem_map.mp u.2
         exact ⟨g, Subtype.ext hg⟩⟩
  letI : IsSimpleGroup ↥group := InfoGeometry.Cantor.SimpleCantorPermutationGroup.isSimpleGroup
  exact e.symm.isSimpleGroup

private def associatorSource (x : ℕ) : ↥TwistedBrinGroup :=
  Generators.associator (Γ := PUnit) (X := ℕ) x

private def flipSource (x : ℕ) : ↥TwistedBrinGroup :=
  Generators.flip (Γ := PUnit) (X := ℕ) x

private theorem associator_flip_noncommute (x : ℕ) :
    (associatorSource x : Equiv.Perm CantorCube) *
      (flipSource x : Equiv.Perm CantorCube) ≠
    (flipSource x : Equiv.Perm CantorCube) *
      (associatorSource x : Equiv.Perm CantorCube) := by
  intro he
  let w : Cube ℕ := fun _ _ => false
  have heval := congrArg (fun p : Equiv.Perm (Cube ℕ) => p
    ((Prefix.oneBit x false).attach ((Prefix.oneBit x false).attach w))) he
  simp only [Equiv.Perm.mul_apply] at heval
  have hleft :
      (associatorSource x : Equiv.Perm (Cube ℕ))
          ((flipSource x : Equiv.Perm (Cube ℕ))
            ((Prefix.oneBit x false).attach ((Prefix.oneBit x false).attach w))) =
        ((Prefix.oneBit x false).comp (Prefix.oneBit x true)).attach w := by
    calc
      _ = (associatorSource x : Equiv.Perm (Cube ℕ))
          ((Prefix.oneBit x true).attach ((Prefix.oneBit x false).attach w)) := by
            rw [flipSource, Generators.flip_attach]
            simp only [Bool.not_false]
      _ = (associatorSource x : Equiv.Perm (Cube ℕ))
          (((Prefix.oneBit x true).comp (Prefix.oneBit x false)).attach w) := by
            rw [Prefix.comp_attach]
      _ = ((Prefix.oneBit x false).comp (Prefix.oneBit x true)).attach w :=
            by simpa [associatorSource] using Generators.associator_middle x w
  have hright :
      (flipSource x : Equiv.Perm (Cube ℕ))
          ((associatorSource x : Equiv.Perm (Cube ℕ))
            ((Prefix.oneBit x false).attach ((Prefix.oneBit x false).attach w))) =
        ((Prefix.oneBit x true).comp (Prefix.oneBit x false)).attach
          ((Prefix.oneBit x false).attach w) := by
    calc
      _ = (flipSource x : Equiv.Perm (Cube ℕ))
          (((Prefix.oneBit x false).comp (Prefix.oneBit x false)).attach
            ((Prefix.oneBit x false).attach w)) := by
              rw [associatorSource, Generators.associator_left]
      _ = (flipSource x : Equiv.Perm (Cube ℕ))
          ((Prefix.oneBit x false).attach
            ((Prefix.oneBit x false).attach ((Prefix.oneBit x false).attach w))) := by
              rw [Prefix.comp_attach]
      _ = (Prefix.oneBit x true).attach
          ((Prefix.oneBit x false).attach ((Prefix.oneBit x false).attach w)) := by
              rw [flipSource, Generators.flip_attach]
              simp only [Bool.not_false]
      _ = ((Prefix.oneBit x true).comp (Prefix.oneBit x false)).attach
          ((Prefix.oneBit x false).attach w) := by
              rw [Prefix.comp_attach]
  have hcoord := congrArg (fun z : Cube ℕ => z x 0) heval
  rw [hleft, hright] at hcoord
  simp only [Prefix.comp, Prefix.oneBit, Prefix.attach] at hcoord
  change false = true at hcoord
  contradiction

/-- The Cantor simple operator group contains a concrete noncommuting pair:
the finite-prefix associator and first-coordinate flip. -/
theorem operatorGroup_noncommutative :
    ∃ U V : ↥operatorGroup, U * V ≠ V * U := by
  let a : ↥TwistedBrinGroup := associatorSource 0
  let f : ↥TwistedBrinGroup := flipSource 0
  let g : ↥group := ⟨cubeEquivCantorWord.permCongrHom a, by
    change cubeEquivCantorWord.permCongrHom a ∈
      TwistedBrinGroup.map cubeEquivCantorWord.permCongrHom.toMonoidHom
    rw [Subgroup.mem_map]
    exact ⟨(a : Equiv.Perm CantorCube), a.property, rfl⟩⟩
  let h : ↥group := ⟨cubeEquivCantorWord.permCongrHom f, by
    change cubeEquivCantorWord.permCongrHom f ∈
      TwistedBrinGroup.map cubeEquivCantorWord.permCongrHom.toMonoidHom
    rw [Subgroup.mem_map]
    exact ⟨(f : Equiv.Perm CantorCube), f.property, rfl⟩⟩
  have hgh : g * h ≠ h * g := by
    intro he
    have hperm := congrArg (fun z : ↥group => (z : Equiv.Perm CantorWord)) he
    apply associator_flip_noncommute 0
    apply cubeEquivCantorWord.permCongrHom.injective
    simpa [g, h] using hperm
  refine ⟨⟨operatorUnitRep g, ?_⟩, ⟨operatorUnitRep h, ?_⟩, ?_⟩
  · rw [operatorGroup, Subgroup.mem_map]
    exact ⟨g, trivial, rfl⟩
  · rw [operatorGroup, Subgroup.mem_map]
    exact ⟨h, trivial, rfl⟩
  · intro hcomm
    apply hgh
    apply operatorUnitRep_injective
    have hval := congrArg (fun x : ↥operatorGroup =>
      (x : (Module.End ℝ (CantorWord → ℝ))ˣ)) hcomm
    change operatorUnitRep g * operatorUnitRep h =
      operatorUnitRep h * operatorUnitRep g at hval
    simpa only [map_mul] using hval

/-- Every finite transposition of Cantor first-bit coordinates is represented
by a unit in the noncommutative operator image of the simple Cantor group. -/
theorem cantorFirstBitSwap_operatorUnit_mem_group (i j : ℕ) :
    operatorUnitRep
      (⟨cantorFirstBitSwap i j, cantorFirstBitSwap_mem_group i j⟩ : ↥group) ∈
        operatorGroup := by
  rw [operatorGroup, Subgroup.mem_map]
  exact ⟨⟨cantorFirstBitSwap i j, cantorFirstBitSwap_mem_group i j⟩,
    trivial, rfl⟩

/-- The represented coordinate transposition acts by inverse reindexing on
real-valued Cantor functions; the operator carrier remains the full
endomorphism algebra, rather than scalar coefficient data. -/
theorem cantorFirstBitSwap_operatorUnit_val_apply (i j : ℕ)
    (f : CantorWord → ℝ) (x : CantorWord) :
    (operatorUnitRep
      (⟨cantorFirstBitSwap i j, cantorFirstBitSwap_mem_group i j⟩ : ↥group) :
        (Module.End ℝ (CantorWord → ℝ))ˣ).val f x =
      f ((cantorFirstBitSwap i j)⁻¹ x) := rfl

end InfoGeometry.Cantor.SimpleCantorOperatorGroup
