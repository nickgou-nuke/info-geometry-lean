/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Cantor.CantorRandomWalk
import InfoGeometry.Cantor.PermutationOperator
import InfoGeometry.RootSystem.D4BitConfigurationAction

/-!
# The D₄ Weyl action on binary Cantor words

The D₄ root lattice is countably infinite, so Boolean configurations indexed
by it can be reindexed as binary sequences. This transports the faithful Weyl
permutation representation to the same carrier used by the Cantor permutation
groups. It does not identify the D₄ Weyl group with the simple Brin--Thompson
subgroup.
-/

noncomputable section

namespace InfoGeometry.RootSystem.D4

open InfoGeometry.Cantor.CantorRandomWalk
open InfoGeometry.Cantor.PermutationOperator

/-- Integer multiples of one simple root give an injective sequence in D₄. -/
def natToLattice (n : ℕ) : Lattice := (n : ℤ) • simpleRootLattice 0

theorem natToLattice_injective : Function.Injective natToLattice := by
  intro m n h
  have h0 := congrArg (fun x : Lattice => x.1 0) h
  exact_mod_cast (by simpa [natToLattice, simpleRootLattice, simpleRoot] using h0)

instance lattice_infinite : Infinite Lattice :=
  Infinite.of_injective natToLattice natToLattice_injective

/-- A classical enumeration of the countably infinite D₄ root lattice. -/
def latticeEquivNat : Lattice ≃ ℕ := by
  haveI : Countable Lattice := inferInstance
  have hcard : Cardinal.mk Lattice = Cardinal.aleph0 := Cardinal.mk_eq_aleph0 Lattice
  letI : Denumerable Lattice := Classical.choice ((Cardinal.denumerable_iff).2 hcard)
  exact Denumerable.eqv Lattice

/-- Reindex lattice-indexed Boolean configurations as infinite binary words. -/
def bitConfigurationEquivCantorWord :
    D4BitConfiguration ≃ CantorWord where
  toFun f n := f (latticeEquivNat.symm n)
  invFun w x := w (latticeEquivNat x)
  left_inv f := by
    funext x
    simp
  right_inv w := by
    funext n
    simp

/-- The D₄ Weyl group acts faithfully by permutations of the binary Cantor
word carrier. -/
def cantorWordPermRep : d4WeylGroup →* Equiv.Perm CantorWord :=
  bitConfigurationEquivCantorWord.permCongrHom.toMonoidHom.comp
    d4BitConfigurationPermRep

theorem cantorWordPermRep_injective : Function.Injective cantorWordPermRep := by
  exact bitConfigurationEquivCantorWord.permCongrHom.injective.comp
    d4BitConfigurationPermRep_injective

/-- The image Weyl subgroup acting on the binary Cantor-word carrier. -/
def cantorWordWeylGroup : Subgroup (Equiv.Perm CantorWord) :=
  (⊤ : Subgroup d4WeylGroup).map cantorWordPermRep

/-- The D₄ Cantor-word permutation acts on real-valued Cantor-word states
by inverse reindexing. -/
def cantorWordOperator (g : d4WeylGroup) :
    Module.End ℝ (CantorWord → ℝ) :=
  operator (R := ℝ) (cantorWordPermRep g)

/-- Package the Cantor-word action as an invertible linear operator. -/
def cantorWordOperatorUnit (g : d4WeylGroup) :
    (Module.End ℝ (CantorWord → ℝ))ˣ :=
  operatorUnit (R := ℝ) (cantorWordPermRep g)

/-- The D₄ Weyl group represented by invertible operators on real-valued
Cantor-word states. -/
def cantorWordOperatorUnitRep : d4WeylGroup →*
    (Module.End ℝ (CantorWord → ℝ))ˣ :=
  operatorUnitRep (X := CantorWord) (R := ℝ) |>.comp cantorWordPermRep

/-- Function probes make the Cantor-word operator representation faithful. -/
theorem cantorWordOperatorUnitRep_injective :
    Function.Injective cantorWordOperatorUnitRep := by
  exact (operatorUnitRep_injective (X := CantorWord) (R := ℝ)).comp
    cantorWordPermRep_injective

/-- The D₄ Cantor-word Weyl group as an actual subgroup of invertible
operators on the real state-function module. -/
def cantorWordOperatorGroup :
    Subgroup (Module.End ℝ (CantorWord → ℝ))ˣ :=
  (⊤ : Subgroup d4WeylGroup).map cantorWordOperatorUnitRep

private theorem adjacentD4Reflections_noncommute :
    simpleReflectionEquiv 0 * simpleReflectionEquiv 1 ≠
      simpleReflectionEquiv 1 * simpleReflectionEquiv 0 := by
  intro he
  have happly := congrArg (fun e : Equiv.Perm Lattice => e (simpleRootLattice 0)) he
  simp only [Equiv.Perm.mul_apply] at happly
  have hcoord := congrArg (fun x : Lattice => x.1 0) happly
  norm_num [simpleReflectionEquiv, reflect_lattice, reflect, dot, simpleRoot,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at hcoord
  norm_num [simpleRootLattice, simpleRoot] at hcoord

/-- Adjacent D₄ reflections remain noncommuting in the Cantor-word
operator image. -/
theorem cantorWordOperatorGroup_noncommutative :
    ∃ U V : ↥cantorWordOperatorGroup, U * V ≠ V * U := by
  let g : d4WeylGroup :=
    ⟨simpleReflectionEquiv 0, simpleReflectionEquiv_mem_d4WeylGroup 0⟩
  let h : d4WeylGroup :=
    ⟨simpleReflectionEquiv 1, simpleReflectionEquiv_mem_d4WeylGroup 1⟩
  have hgh : g * h ≠ h * g := by
    intro he
    apply adjacentD4Reflections_noncommute
    exact congrArg (fun x : d4WeylGroup => (x : Equiv.Perm Lattice)) he
  refine ⟨⟨cantorWordOperatorUnitRep g, ?_⟩,
    ⟨cantorWordOperatorUnitRep h, ?_⟩, ?_⟩
  · rw [cantorWordOperatorGroup, Subgroup.mem_map]
    exact ⟨g, trivial, rfl⟩
  · rw [cantorWordOperatorGroup, Subgroup.mem_map]
    exact ⟨h, trivial, rfl⟩
  · intro hcomm
    apply hgh
    apply cantorWordOperatorUnitRep_injective
    have hval := congrArg (fun x : ↥cantorWordOperatorGroup =>
      (x : (Module.End ℝ (CantorWord → ℝ))ˣ)) hcomm
    change cantorWordOperatorUnitRep g * cantorWordOperatorUnitRep h =
      cantorWordOperatorUnitRep h * cantorWordOperatorUnitRep g at hval
    simpa only [map_mul] using hval

@[simp] theorem cantorWord_smul_apply (g : d4WeylGroup) (w : CantorWord) (n : ℕ) :
    (cantorWordPermRep g w) n =
      w (latticeEquivNat (((g⁻¹ : d4WeylGroup) : Lattice ≃ Lattice)
        (latticeEquivNat.symm n))) := by
  rfl

end InfoGeometry.RootSystem.D4

end
