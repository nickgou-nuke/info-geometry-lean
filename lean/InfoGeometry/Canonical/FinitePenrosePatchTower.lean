import InfoGeometry.Canonical.FinitePenrosePatchCategory

/-!
# Finite Penrose patch towers

This file packages monotone towers of finite Penrose patches and realizes them as
functors out of the preorder category on `ℕ`.

It is the bridge from discrete finite patches to later colimit-style Penrose
limit constructions.
-/

namespace FinitePenrosePatchTower

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.FinitePenrosePatchCategory
open InfoGeometry.Canonical.DiscretePenroseSpinNet

universe u v

section Basic

variable {α : Type u} {𝕜 T D : Type u}
variable [PartialOrder α]
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]

/-- A monotone tower of finite patches inside a fixed discrete Penrose spin net. -/
structure PatchTower (S : SpinNet α 𝕜 T D) where
  stage : ℕ → FinitePatch (α := α)
  bond : ∀ n, stage n ≤ stage (n + 1)

variable {S : SpinNet α 𝕜 T D}

/-- The stage carriers are monotone along the natural-number order. -/
theorem stage_mono (Twr : PatchTower S) {m n : ℕ} (h : m ≤ n) :
    Twr.stage m ≤ Twr.stage n := by
  induction h with
  | refl =>
      exact le_rfl
  | @step n h ih =>
      exact le_trans ih (Twr.bond n)

/-- A patch tower is a functor from the preorder category on `ℕ`. -/
def toFunctor (Twr : PatchTower S) : ℕ ⥤ FinitePatch (α := α) where
  obj n := Twr.stage n
  map {m n} h := PLift.up (stage_mono Twr h.down.down)
  map_id := by
    intro n
    apply Subsingleton.elim
  map_comp := by
    intro a b c f g
    apply Subsingleton.elim

/-- An upper-bound patch contains every stage of the tower. -/
def TowerUpperBound (Twr : PatchTower S) (apex : FinitePatch (α := α)) : Prop :=
  ∀ n, Twr.stage n ≤ apex

/-- Any upper-bound patch gives a cocone over the patch tower. -/
def coconeOfUpperBound
    (Twr : PatchTower S)
    {apex : FinitePatch (α := α)}
    (hub : TowerUpperBound Twr apex) :
    Cocone (toFunctor Twr) :=
  patchCoconeOfUpperBound (α := α) (F := toFunctor Twr) hub

/-- Local states at every stage functorially embed into any upper-bound patch. -/
theorem localState_reaches_upperBound
    (Twr : PatchTower S)
    {apex : FinitePatch (α := α)}
    (hub : TowerUpperBound Twr apex)
    (n : ℕ)
    (x : (localStateFunctor (α := α) S).obj (Twr.stage n)) :
    (localStateFunctor (α := α) S).map ((coconeOfUpperBound Twr hub).ι.app n) x =
      mapLocalState (α := α) S (PLift.up (hub n)) x :=
  rfl

end Basic

end FinitePenrosePatchTower
