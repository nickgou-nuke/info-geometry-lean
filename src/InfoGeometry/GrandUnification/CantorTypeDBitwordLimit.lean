/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import InfoGeometry.GrandUnification.TypeDWeylSemidirectAction

/-!
# Stream of Consciousness Extraction & Causal Poset: The Infinite Type-D Cantor Lattice

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Finite Type-D bitword spaces $\mathbb{Z}_2^n = \mathrm{Fin}\,n \to \mathrm{ZMod}\,2$,
    Hamming parity $\sum_{i} w_i \in \mathrm{ZMod}\,2$, and even-parity subgroups
    (`TypeDTransitionSubgroup`, `TypeDEvenParity`).
- BUCKET 2 (Deconfabulation):
  * Eliminated the `sorry` in `typeDDiagram.map_comp` by proving exact functoriality of
    zero-padded bitword extensions (`padZeros_comp`, `iteratedExtendParityHom_comp`)
    over the filtered poset category $\mathbb{N}$ in both `ModuleCat (ZMod 2)` and
    `AddCommGrpCat`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `parity_extendBitword` and `parity_iteratedExtendBitword`: zero-padding preserves
    total $\mathrm{ZMod}\,2$ parity across all finite stages $n \le m$.
  * `iteratedExtendParityHom_succ` and `iteratedExtendParityHom_comp`: exact one-step
    and transitive composition laws on `TypeDEvenParity`.
  * `typeDDiagram`, `cantorTypeDLattice`, `injectFiniteState`,
    `injectFiniteState_iteratedExtend`, and `injectFiniteState_extendParityHom`:
    categorical filtered colimit of `TypeDEvenParity n` in `AddCommGrpCat` and lossless
    commuting cocone injections.
-/

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.GrandUnification.TypeDWeyl

namespace InfoGeometry.GrandUnification.CantorLimit

/-- Zero-padding linear map from `Bitword (Fin i)` to `Bitword (Fin j)` for `i ≤ j`. -/
def padZeros (i j : ℕ) (_hij : i ≤ j) : Bitword (Fin i) →ₗ[ZMod 2] Bitword (Fin j) where
  toFun w k := if h : k.val < i then w ⟨k.val, h⟩ else 0
  map_add' x y := by ext k; dsimp; split_ifs with h <;> rfl
  map_smul' c x := by ext k; dsimp; split_ifs with h <;> rfl

/-- Zero-padding preserves `bitwordParity` for all `i ≤ j`. -/
lemma padZeros_parity (i j : ℕ) (hij : i ≤ j) (w : Bitword (Fin i)) :
    bitwordParity (padZeros i j hij w) = bitwordParity w := by
  induction' j, hij using Nat.le_induction with k hk ih
  · dsimp [bitwordParity, padZeros, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro x _
    have h_lt : x.val < i := x.isLt
    simp [h_lt]
  · rw [← ih]
    dsimp [bitwordParity, padZeros, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Fin.sum_univ_castSucc]
    have h_eq :
        (∑ x : Fin k, if h : (Fin.castSucc x).val < i then w ⟨(Fin.castSucc x).val, h⟩ else 0) =
          ∑ x : Fin k, if h : x.val < i then w ⟨x.val, h⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rfl
    rw [h_eq]
    have h_last : (if h : (Fin.last k).val < i then w ⟨(Fin.last k).val, h⟩ else 0) = 0 := by
      have h_not : ¬((Fin.last k).val < i) := by
        have h_eq_k : (Fin.last k).val = k := Fin.val_last k
        rw [h_eq_k]
        omega
      rw [dite_eq_right h_not]
    rw [h_last, add_zero]

/-- Transition linear map on `TypeDTransitionSubgroup` induced by `padZeros`. -/
def typeDTransitionMap (i j : ℕ) (hij : i ≤ j) :
    TypeDTransitionSubgroup (Fin i) →ₗ[ZMod 2] TypeDTransitionSubgroup (Fin j) where
  toFun w := ⟨padZeros i j hij w.val, by
    have hw := w.property
    change bitwordParity w.val = 0 at hw
    change bitwordParity (padZeros i j hij w.val) = 0
    rw [padZeros_parity]
    exact hw⟩
  map_add' x y := Subtype.ext ((padZeros i j hij).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((padZeros i j hij).map_smul c x.val)

/-- Composition of `padZeros` across `i ≤ j ≤ k` agrees with `padZeros i k`. -/
lemma padZeros_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) (w : Bitword (Fin i)) :
    padZeros j k hjk (padZeros i j hij w) = padZeros i k hik w := by
  ext x
  dsimp [padZeros]
  by_cases h_i : x.val < i
  · have h_j : x.val < j := lt_of_lt_of_le h_i hij
    simp [h_i, h_j]
  · by_cases h_j : x.val < j
    · simp [h_i, h_j]
    · simp [h_i, h_j]

/-- Filtered system of `TypeDTransitionSubgroup (Fin n)` in `ModuleCat (ZMod 2)`. -/
def typeDSystem : ℕ ⥤ ModuleCat (ZMod 2) where
  obj n := ModuleCat.of (ZMod 2) (TypeDTransitionSubgroup (Fin n))
  map {i j} hij := ModuleCat.ofHom (typeDTransitionMap i j (leOfHom hij))
  map_id i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ⟨w, hw⟩
    apply Subtype.ext
    ext k
    dsimp [typeDTransitionMap, padZeros]
    simp
  map_comp {i j k} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ⟨w, hw⟩
    apply Subtype.ext
    dsimp [ModuleCat.ofHom, typeDTransitionMap]
    exact (padZeros_comp i j k (leOfHom f) (leOfHom g) (leOfHom (f ≫ g)) w).symm

/-- Colimit of `typeDSystem` in `ModuleCat (ZMod 2)`. -/
noncomputable def TypeDCantorLimit := colimit typeDSystem

end InfoGeometry.GrandUnification.CantorLimit

namespace InfoGeometry.GrandUnification.CantorTypeDBitwordLimit

/-!
# Phase 1: Finite Bitwords and Parity Subgroups over Fin n
We instantiate the ATOMiK bitword logic over the indexing set `Fin n` to allow
for sequential extension.
-/

/-- The space of hardware states of length `n`. -/
abbrev Bitword (n : ℕ) := Fin n → ZMod 2

/-- The total parity (Hamming weight mod 2) of a bitword. -/
def parity {n : ℕ} (w : Bitword n) : ZMod 2 :=
  ∑ i : Fin n, w i

/-- The Type-D Subregular Constraint: the subgroup of states with even parity,
simulating the $D_n$ root lattice. -/
def TypeDEvenParity (n : ℕ) : AddSubgroup (Bitword n) where
  carrier := { w | parity w = 0 }
  add_mem' {a b} ha hb := by
    change parity a = 0 at ha
    change parity b = 0 at hb
    change parity (a + b) = 0
    unfold parity at ha hb ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, ha, hb, add_zero]
  zero_mem' := by
    change parity 0 = 0
    unfold parity
    exact Finset.sum_const_zero
  neg_mem' {a} ha := by
    change parity a = 0 at ha
    change parity (-a) = 0
    unfold parity at ha ⊢
    simp only [Pi.neg_apply, Finset.sum_neg_distrib, ha, neg_zero]

/-!
# Phase 2 & 3: Extension Maps and Parity Preservation
To build the limit $n \to \infty$, we inject length `n` bitwords into
length `n + 1` bitwords (and generally length `m` for `n ≤ m`) by padding new
coordinates with `0`.
-/

/-- Pads a bitword of length `n` to length `n + 1` by appending a `0`. -/
def extendBitword {n : ℕ} (w : Bitword n) : Bitword (n + 1) :=
  fun i => if h : (i : ℕ) < n then w ⟨(i : ℕ), h⟩ else 0

/-- Appending a zero strictly preserves the total parity of the state. -/
lemma parity_extendBitword {n : ℕ} (w : Bitword n) :
    parity (extendBitword w) = parity w :=
  InfoGeometry.GrandUnification.CantorLimit.padZeros_parity n (n + 1) (Nat.le_succ n) w

/-- The one-step transition map restricted to the `TypeDEvenParity` subgroups. -/
def extendParityHom {n : ℕ} : TypeDEvenParity n →+ TypeDEvenParity (n + 1) where
  toFun w := ⟨extendBitword w.val, by
    have hp : parity w.val = 0 := w.property
    change parity (extendBitword w.val) = 0
    rw [parity_extendBitword, hp]⟩
  map_zero' := by
    ext i
    dsimp [extendBitword]
    split_ifs <;> rfl
  map_add' a b := by
    ext i
    dsimp [extendBitword]
    split_ifs <;> rfl

/-- Iterated zero-padding of a bitword of length `n` to length `m` (`n ≤ m`). -/
def iteratedExtendBitword {n m : ℕ} (_h : n ≤ m) (w : Bitword n) : Bitword m :=
  fun i => if hi : (i : ℕ) < n then w ⟨(i : ℕ), hi⟩ else 0

/-- Iterated zero-padding preserves `parity` for any `n ≤ m`. -/
lemma parity_iteratedExtendBitword {n m : ℕ} (h : n ≤ m) (w : Bitword n) :
    parity (iteratedExtendBitword h w) = parity w :=
  InfoGeometry.GrandUnification.CantorLimit.padZeros_parity n m h w

/-- Iterated extension `AddMonoidHom` on `TypeDEvenParity` for `n ≤ m`. -/
def iteratedExtendParityHom {n m : ℕ} (h : n ≤ m) :
    TypeDEvenParity n →+ TypeDEvenParity m where
  toFun w := ⟨iteratedExtendBitword h w.val, by
    have hp : parity w.val = 0 := w.property
    change parity (iteratedExtendBitword h w.val) = 0
    rw [parity_iteratedExtendBitword, hp]⟩
  map_zero' := by
    ext i
    dsimp [iteratedExtendBitword]
    split_ifs <;> rfl
  map_add' a b := by
    ext i
    dsimp [iteratedExtendBitword]
    split_ifs <;> rfl

/-- At `n = m`, `iteratedExtendParityHom` is the identity homomorphism. -/
lemma iteratedExtendParityHom_refl (n : ℕ) :
    iteratedExtendParityHom (le_refl n) = AddMonoidHom.id (TypeDEvenParity n) := by
  ext w i
  dsimp [iteratedExtendParityHom, iteratedExtendBitword]
  simp [i.isLt]

/-- For `m = n + 1`, `iteratedExtendParityHom` coincides with `extendParityHom`. -/
lemma iteratedExtendParityHom_succ (n : ℕ) :
    iteratedExtendParityHom (Nat.le_succ n) = extendParityHom := by
  ext w i
  rfl

/-- Functorial composition law for `iteratedExtendParityHom` across `n ≤ m ≤ k`. -/
lemma iteratedExtendParityHom_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    (iteratedExtendParityHom hmk).comp (iteratedExtendParityHom hnm) =
      iteratedExtendParityHom (le_trans hnm hmk) := by
  ext w x
  dsimp [iteratedExtendParityHom, iteratedExtendBitword]
  by_cases h_n : (x : ℕ) < n
  · have h_m : (x : ℕ) < m := lt_of_lt_of_le h_n hnm
    simp [h_n, h_m]
  · by_cases h_m : (x : ℕ) < m
    · simp [h_n, h_m]
    · simp [h_n, h_m]

/-!
# Phase 4 & 5: The Filtered Diagram and the Cantor Limit
We construct the functor from the poset `ℕ` into `AddCommGrpCat`,
then take its categorical colimit.
-/

/-- The underlying categorical objects: the even-parity subgroups as objects of `AddCommGrpCat`. -/
def typeDObject (n : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (TypeDEvenParity n)

/-- Iterated extension morphism `typeDObject n ⟶ typeDObject m` in `AddCommGrpCat`. -/
def iteratedExtend {n m : ℕ} (h : n ≤ m) : typeDObject n ⟶ typeDObject m :=
  AddCommGrpCat.ofHom (iteratedExtendParityHom h)

/-- The Filtered Diagram of finite ATOMiK Type-D states over `ℕ`. -/
def typeDDiagram : ℕ ⥤ AddCommGrpCat where
  obj n := typeDObject n
  map {n m} (h : n ⟶ m) := iteratedExtend (leOfHom h)
  map_id n := by
    apply AddCommGrpCat.ext
    intro w
    change iteratedExtendParityHom (le_refl n) w = w
    rw [iteratedExtendParityHom_refl]
    rfl
  map_comp {n m k} f g := by
    apply AddCommGrpCat.ext
    intro w
    change iteratedExtendParityHom (leOfHom (f ≫ g)) w =
      iteratedExtendParityHom (leOfHom g) (iteratedExtendParityHom (leOfHom f) w)
    rw [← iteratedExtendParityHom_comp (leOfHom f) (leOfHom g)]
    rfl

/-- The Infinite Type-D Cantor Lattice: the categorical colimit of the finite
even-parity bitword subgroups as $n \to \infty$ in `AddCommGrpCat`. -/
noncomputable def cantorTypeDLattice : AddCommGrpCat :=
  colimit typeDDiagram

/-- Canonical cocone injection of any finite Type-D hardware state into the
infinite Cantor Lattice `cantorTypeDLattice`. -/
noncomputable def injectFiniteState (n : ℕ) (state : TypeDEvenParity n) :
    (cantorTypeDLattice : Type) :=
  colimit.ι typeDDiagram n state

/-- Cocone compatibility: padding a finite state to stage `m` (`n ≤ m`) and injecting
into `cantorTypeDLattice` yields the exact same element as injecting at stage `n`. -/
theorem injectFiniteState_iteratedExtend {n m : ℕ} (h : n ≤ m) (state : TypeDEvenParity n) :
    injectFiniteState m (iteratedExtendParityHom h state) = injectFiniteState n state := by
  unfold injectFiniteState cantorTypeDLattice
  have h_nat := colimit.w typeDDiagram (homOfLE h)
  have h_eval := congrArg (fun (f : typeDObject n ⟶ colimit typeDDiagram) => f state) h_nat
  exact h_eval

/-- One-step cocone invariance: appending a `0` via `extendParityHom` preserves the image
in `cantorTypeDLattice`. -/
theorem injectFiniteState_extendParityHom (n : ℕ) (state : TypeDEvenParity n) :
    injectFiniteState (n + 1) (extendParityHom state) = injectFiniteState n state := by
  rw [← iteratedExtendParityHom_succ n]
  exact injectFiniteState_iteratedExtend (Nat.le_succ n) state

end InfoGeometry.GrandUnification.CantorTypeDBitwordLimit
