/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.RootSystem.ExceptionalRootLatticeWeyl

/-!
# Exceptional root Weyl symmetries as operators

The root-lattice reflection group acts on real-valued functions on the root
lattice by inverse reindexing. This gives a representation by invertible
endomorphisms, retaining operator composition as group multiplication.
-/

noncomputable section

namespace InfoGeometry.RootSystem.Exceptional

open InfoGeometry.Exceptional.CFSGPort.Chevalley

/-- The operator on root-lattice functions induced by a Weyl symmetry. -/
def rootWeylOperator (τ : Tag) (w : rootLatticeWeylGroup τ) :
    Module.End ℝ (RootLattice τ → ℝ) where
  toFun f x := f (((w⁻¹ : rootLatticeWeylGroup τ) : Equiv.Perm (RootLattice τ)) x)
  map_add' f g := by funext x; rfl
  map_smul' c f := by funext x; rfl

@[simp] theorem rootWeylOperator_apply (τ : Tag)
    (w : rootLatticeWeylGroup τ) (f : RootLattice τ → ℝ) (x : RootLattice τ) :
    rootWeylOperator τ w f x =
      f (((w⁻¹ : rootLatticeWeylGroup τ) : Equiv.Perm (RootLattice τ)) x) := rfl

/-- The Weyl group represented by its linear operators. -/
def rootWeylOperatorRep (τ : Tag) :
    rootLatticeWeylGroup τ →* (Module.End ℝ (RootLattice τ → ℝ)) where
  toFun := rootWeylOperator τ
  map_one' := by ext f x; rfl
  map_mul' g h := by ext f x; rfl

/-- The operator represented by a Weyl element, packaged with its inverse. -/
def rootWeylOperatorUnit (τ : Tag) (w : rootLatticeWeylGroup τ) :
    (Module.End ℝ (RootLattice τ → ℝ))ˣ where
  val := rootWeylOperator τ w
  inv := rootWeylOperator τ w⁻¹
  val_inv := by ext f x; simp [rootWeylOperator]
  inv_val := by ext f x; simp [rootWeylOperator]

/-- The operator-unit representation of the exceptional Weyl group. -/
def rootWeylOperatorUnitRep (τ : Tag) :
    rootLatticeWeylGroup τ →* (Module.End ℝ (RootLattice τ → ℝ))ˣ where
  toFun := rootWeylOperatorUnit τ
  map_one' := by apply Units.ext; ext f x; rfl
  map_mul' g h := by apply Units.ext; ext f x; rfl

/-- The operator-unit representation retains every root-lattice symmetry. -/
theorem rootWeylOperatorUnitRep_injective (τ : Tag) :
    Function.Injective (rootWeylOperatorUnitRep τ) := by
  intro g h hgh
  have hval : rootWeylOperator τ g = rootWeylOperator τ h :=
    congrArg (fun u : (Module.End ℝ (RootLattice τ → ℝ))ˣ =>
      (u : Module.End ℝ (RootLattice τ → ℝ))) hgh
  have hinv : (g⁻¹ : Equiv.Perm (RootLattice τ)) =
      (h⁻¹ : Equiv.Perm (RootLattice τ)) := by
    apply Equiv.ext
    intro x
    let gx := ((g⁻¹ : Equiv.Perm (RootLattice τ)) x)
    let hx := ((h⁻¹ : Equiv.Perm (RootLattice τ)) x)
    let δ : RootLattice τ → ℝ := fun y => if y = gx then 1 else 0
    have heval := congrArg (fun T : Module.End ℝ (RootLattice τ → ℝ) => T δ x) hval
    change δ gx = δ hx at heval
    have hargs : hx = gx := by
      by_cases h : hx = gx
      · exact h
      · simp [δ, gx, hx] at heval
        exact False.elim (h heval)
    change gx = hx
    exact hargs.symm
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hsymm := congrArg (fun p : Equiv.Perm (RootLattice τ) => p x)
    (congrArg Inv.inv hinv)
  simpa using hsymm

/-- The faithful operator representation preserves every noncommuting pair
of root-lattice Weyl symmetries. -/
theorem rootWeylOperatorUnitRep_ne_mul_swap (τ : Tag)
    (g h : rootLatticeWeylGroup τ) (hgh : g * h ≠ h * g) :
    rootWeylOperatorUnitRep τ g * rootWeylOperatorUnitRep τ h ≠
      rootWeylOperatorUnitRep τ h * rootWeylOperatorUnitRep τ g := by
  intro hcomm
  apply hgh
  apply rootWeylOperatorUnitRep_injective τ
  simpa only [map_mul] using hcomm

/-- Weyl symmetry operators form a concrete subgroup of the invertible
operator group on root-lattice functions. -/
def rootOperatorWeylGroup (τ : Tag) :
    Subgroup (Module.End ℝ (RootLattice τ → ℝ))ˣ :=
  (⊤ : Subgroup (rootLatticeWeylGroup τ)).map (rootWeylOperatorUnitRep τ)

/-- Every simple reflection is represented inside the operator Weyl group. -/
theorem simpleReflectionOperator_mem_rootOperatorWeylGroup
    (τ : Tag) (i : Fin τ.rank) :
    rootWeylOperatorUnitRep τ ⟨simpleReflection τ i,
      Subgroup.subset_closure ⟨i, rfl⟩⟩ ∈ rootOperatorWeylGroup τ := by
  rw [rootOperatorWeylGroup, Subgroup.mem_map]
  exact ⟨⟨simpleReflection τ i, Subgroup.subset_closure ⟨i, rfl⟩⟩, trivial, rfl⟩

end InfoGeometry.RootSystem.Exceptional
