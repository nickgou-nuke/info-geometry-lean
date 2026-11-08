/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib

/-!
# Permutations as operators on function spaces

An equivalence acts on functions by inverse reindexing. This shared
representation is used by the Cantor, Coxeter, and root-lattice symmetry
owners, so the same permutation action is not reimplemented at each carrier.
-/

noncomputable section

namespace InfoGeometry.Cantor.PermutationOperator

variable {X R : Type*} [Semiring R]

/-- The linear operator induced by a permutation through inverse
reindexing. -/
def operator (p : Equiv.Perm X) : Module.End R (X → R) where
  toFun f x := f (p⁻¹ x)
  map_add' f g := by funext x; rfl
  map_smul' c f := by funext x; rfl

@[simp] theorem operator_apply (p : Equiv.Perm X) (f : X → R) (x : X) :
    operator (R := R) p f x = f (p⁻¹ x) := rfl

/-- The permutation homomorphism into linear endomorphisms of the function
space. -/
def operatorRep : Equiv.Perm X →* Module.End R (X → R) where
  toFun := operator (R := R)
  map_one' := by ext f x; rfl
  map_mul' p q := by ext f x; rfl

/-- The invertible operator induced by a permutation. -/
def operatorUnit (p : Equiv.Perm X) : (Module.End R (X → R))ˣ where
  val := operator (R := R) p
  inv := operator (R := R) p⁻¹
  val_inv := by ext f x; simp [operator]
  inv_val := by ext f x; simp [operator]

/-- The permutation representation on the units of the function-space
endomorphism algebra. -/
def operatorUnitRep : Equiv.Perm X →* (Module.End R (X → R))ˣ where
  toFun := operatorUnit (R := R)
  map_one' := by apply Units.ext; ext f x; rfl
  map_mul' p q := by apply Units.ext; ext f x; rfl

/-- If zero and one differ, function evaluations separate the permutation
operators, so the unit representation is faithful. -/
theorem operatorUnitRep_injective [Nontrivial R] :
    Function.Injective (operatorUnitRep (X := X) (R := R)) := by
  classical
  intro p q hpq
  have hop : operator (R := R) p = operator (R := R) q :=
    congrArg (fun u : (Module.End R (X → R))ˣ =>
      (u : Module.End R (X → R))) hpq
  have hinv : p⁻¹ = q⁻¹ := by
    apply Equiv.ext
    intro x
    let px := p⁻¹ x
    let qx := q⁻¹ x
    let δ : X → R := fun y => if y = px then 1 else 0
    have heval := congrArg (fun T : Module.End R (X → R) => T δ x) hop
    change δ px = δ qx at heval
    have hpoint : qx = px := by
      by_cases h : qx = px
      · exact h
      · simp [δ, px, qx] at heval
        exact False.elim (h heval)
    change px = qx
    exact hpoint.symm
  exact congrArg Inv.inv hinv

end InfoGeometry.Cantor.PermutationOperator

end
