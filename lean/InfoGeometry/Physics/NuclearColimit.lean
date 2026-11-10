/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearShellModel
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Categorical colimit of finite nuclear shell-state modules

For each shell-capacity cutoff `n`, `ShellState n` is the module of coefficient
vectors on the `2n + 1` shell slots owned by `NuclearShellModel`. The bonding
maps extend a state by zero into the larger cutoff. The limit object below is
Mathlib's categorical colimit in `ModuleCat`; it is not encoded as a fixed
natural number or a finite-dimensional operator carrier.

#### BUCKET 1: CLOSED FINITE THEOREMS

The capacity growth, finite-stage module structure, injective zero-extension
maps, and their compatibility with the categorical colimit injections are
proved below.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None; these results use only the stated field and cutoff hypotheses.

#### BUCKET 3: SCOPE BOUNDARY

No shell pairing or physical Hamiltonian has yet been defined on these state
modules, so pairing preservation and nuclear dynamics are not claimed here.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearColimit

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Physics.NuclearShellModel

variable {𝒦 : Type*} [Field 𝒦]

/-- Coefficient vectors on the slots of the shell-capacity cutoff `n`. -/
abbrev ShellState (n : ℕ) := Fin (shell_capacity n) → 𝒦

/-- Shell capacity is monotone in its angular-momentum cutoff. -/
theorem shell_capacity_mono {n m : ℕ} (h : n ≤ m) :
    shell_capacity n ≤ shell_capacity m := by
  change 2 * n + 1 ≤ 2 * m + 1
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1

/-- The capacity strictly increases when one shell layer is added. -/
theorem shell_capacity_succ (n : ℕ) :
    shell_capacity n < shell_capacity (n + 1) := by
  dsimp [shell_capacity]
  omega

/-- Zero-extension of a shell state from cutoff `n` to a larger cutoff `m`. -/
def shellPad {n m : ℕ} (_h : n ≤ m) (x : ShellState (𝒦 := 𝒦) n) :
    ShellState (𝒦 := 𝒦) m := fun i =>
  if hi : i.val < shell_capacity n then x ⟨i.val, hi⟩ else 0

/-- The zero-extension map is linear. -/
def shellPadLinearMap (n m : ℕ) (h : n ≤ m) :
    ShellState (𝒦 := 𝒦) n →ₗ[𝒦] ShellState (𝒦 := 𝒦) m where
  toFun := shellPad h
  map_add' x y := by
    funext i
    by_cases hi : i.val < shell_capacity n <;> simp [shellPad, hi]
  map_smul' a x := by
    funext i
    by_cases hi : i.val < shell_capacity n <;> simp [shellPad, hi]

/-- The successor-cutoff inclusion, now realized as an actual linear map. -/
def shell_inclusion (n : ℕ) :
    ShellState (𝒦 := 𝒦) n →ₗ[𝒦] ShellState (𝒦 := 𝒦) (n + 1) :=
  shellPadLinearMap (𝒦 := 𝒦) n (n + 1) (Nat.le_succ n)

/-- Zero-extension preserves every coordinate already present at stage `n`. -/
theorem shellPad_coordinate {n m : ℕ} (h : n ≤ m)
    (x : ShellState (𝒦 := 𝒦) n) (i : Fin (shell_capacity n)) :
    shellPad h x ⟨i.val, Nat.lt_of_lt_of_le i.isLt (shell_capacity_mono h)⟩ = x i := by
  change (if hi : i.val < shell_capacity n then x ⟨i.val, hi⟩ else 0) = x i
  rw [dite_eq_left i.isLt]

/-- The zero-extension bond has no kernel. -/
theorem shellPadLinearMap_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (shellPadLinearMap (𝒦 := 𝒦) n m h) := by
  intro x y hxy
  ext i
  have hcoord := congrFun hxy
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt (shell_capacity_mono h)⟩
  simpa [shellPadLinearMap, shellPad, i.isLt] using hcoord

/-- Consecutive zero-extensions compose to the direct zero-extension. -/
theorem shellPadLinearMap_comp (n m l : ℕ) (hnm : n ≤ m) (hml : m ≤ l) :
    (shellPadLinearMap (𝒦 := 𝒦) m l hml).comp
        (shellPadLinearMap (𝒦 := 𝒦) n m hnm) =
      shellPadLinearMap (𝒦 := 𝒦) n l (hnm.trans hml) := by
  ext x i
  by_cases hi : i.val < shell_capacity n
  · have him : i.val < shell_capacity m :=
      Nat.lt_of_lt_of_le hi (shell_capacity_mono hnm)
    have hil : i.val < shell_capacity l :=
      Nat.lt_of_lt_of_le him (shell_capacity_mono hml)
    simp [shellPadLinearMap, shellPad, hi, him]
  · simp [shellPadLinearMap, shellPad, hi]

/-- The system of finite shell-state modules with zero-extension bonds. -/
def shellStateFunctor : ℕ ⥤ ModuleCat 𝒦 where
  obj n := ModuleCat.of 𝒦 (ShellState (𝒦 := 𝒦) n)
  map f := ModuleCat.ofHom <|
    shellPadLinearMap (𝒦 := 𝒦) _ _ (leOfHom f)
  map_id n := by
    ext x i
    simp [shellPadLinearMap, shellPad]
  map_comp {n m l} f g := by
    apply ModuleCat.hom_ext
    exact (shellPadLinearMap_comp (𝒦 := 𝒦) n m l (leOfHom f) (leOfHom g)).symm

/-- The actual categorical colimit of all finite nuclear shell-state modules. -/
noncomputable abbrev ShellStateColimit (𝒦 : Type*) [Field 𝒦] :=
  colimit (shellStateFunctor (𝒦 := 𝒦))

/-- The nuclear shell-state colimit, as a categorical colimit object. -/
noncomputable abbrev shell_colimit := ShellStateColimit 𝒦

/-- Canonical map from a fixed shell cutoff into the categorical colimit. -/
noncomputable def shellStateInjection (𝒦 : Type*) [Field 𝒦] (n : ℕ) :
    ShellState (𝒦 := 𝒦) n →ₗ[𝒦] ShellStateColimit 𝒦 :=
  (colimit.ι (shellStateFunctor (𝒦 := 𝒦)) n).hom

/-- The colimit injections identify a state with its zero-extension to every
larger cutoff. -/
@[simp] theorem shellStateInjection_bond {n m : ℕ} (h : n ≤ m)
    (x : ShellState (𝒦 := 𝒦) n) :
    shellStateInjection 𝒦 m
      ((shellStateFunctor (𝒦 := 𝒦)).map (homOfLE h) x) =
        shellStateInjection 𝒦 n x := by
  exact congrArg (fun q => q.hom x)
    (colimit.w (shellStateFunctor (𝒦 := 𝒦)) (homOfLE h))

/-- Well-definedness of the colimit identifications along any cutoff inclusion. -/
theorem colimit_well_defined {n m : ℕ} (h : n ≤ m)
    (x : ShellState (𝒦 := 𝒦) n) :
    shellStateInjection 𝒦 m
        ((shellStateFunctor (𝒦 := 𝒦)).map (homOfLE h) x) =
      shellStateInjection 𝒦 n x := by
  change ((colimit.ι (shellStateFunctor (𝒦 := 𝒦)) m).hom
      (((shellStateFunctor (𝒦 := 𝒦)).map (homOfLE h)) x)) =
    ((colimit.ι (shellStateFunctor (𝒦 := 𝒦)) n).hom x)
  exact congrArg (fun q => q.hom x)
    (colimit.w (shellStateFunctor (𝒦 := 𝒦)) (homOfLE h))

/-- The dimension of a shell-state head is exactly its number of shell slots. -/
theorem shellState_finrank (n : ℕ) :
    Module.finrank 𝒦 (ShellState (𝒦 := 𝒦) n) = shell_capacity n := by
  change Module.finrank 𝒦 (Fin (shell_capacity n) → 𝒦) = shell_capacity n
  simp

end InfoGeometry.Physics.NuclearColimit
