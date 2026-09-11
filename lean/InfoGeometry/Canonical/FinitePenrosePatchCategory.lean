import InfoGeometry.Canonical.DiscretePenroseSpinNet
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Penrose patch category

For a fixed discrete Penrose spin net, this file builds the finite-patch layer:

* finite patch objects;
* patch inclusions as categorical arrows;
* restricted forward/backward cones;
* local-state transport along patch inclusions;
* cocones over patch diagrams from upper-bound patches.

This is the finite discrete graph / category layer beneath any later Penrose
colimit theorem.
-/

namespace InfoGeometry.Canonical.FinitePenrosePatchCategory

open CategoryTheory
open CategoryTheory.Limits
open Set
open InfoGeometry.Canonical.DiscretePenroseSpinNet

universe u v w

section PatchOrder

variable {α : Type u}

/-- A finite patch is just a finite set of events. -/
abbrev FinitePatch := Finset α

namespace FinitePatch

/-- Projection-compatible name for the native finite-set carrier. -/
abbrev carrier (P : FinitePatch (α := α)) : Finset α := P

end FinitePatch

@[ext] theorem FinitePatch.ext {P Q : FinitePatch (α := α)}
    (h : P.carrier = Q.carrier) : P = Q := by
  exact h

@[simp] theorem patch_le_def {P Q : FinitePatch (α := α)} :
    P ≤ Q ↔ P.carrier ⊆ Q.carrier :=
  Iff.rfl

/-- Patch arrows are inclusions of finite carriers. -/
abbrev PatchHom (P Q : FinitePatch (α := α)) : Type := PLift (P ≤ Q)

instance : Category (FinitePatch (α := α)) where
  Hom P Q := PatchHom P Q
  id P := PLift.up le_rfl
  comp f g := PLift.up (show _ ≤ _ from le_trans f.down g.down)

instance {P Q : FinitePatch (α := α)} : Subsingleton (P ⟶ Q) := by
  change Subsingleton (PLift (P ≤ Q))
  infer_instance

@[simp] theorem patch_comp_down {P Q R : FinitePatch (α := α)}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    ((f ≫ g).down : P ≤ R) = le_trans f.down g.down :=
  rfl

end PatchOrder

section SpinNetPatches

variable {α : Type u} {𝕜 T D : Type u}
variable [PartialOrder α]
variable [CommRing 𝕜]
variable [AddCommGroup T] [Module 𝕜 T]
variable [AddCommGroup D] [Module 𝕜 D]

variable (S : SpinNet α 𝕜 T D)

/-- Forward cone restricted to a finite patch. -/
def forwardConeIn (P : FinitePatch (α := α)) (a : α) : Set α :=
  {b | b ∈ P.carrier ∧ a ≤ b}

/-- Backward cone restricted to a finite patch. -/
def backwardConeIn (P : FinitePatch (α := α)) (a : α) : Set α :=
  {b | b ∈ P.carrier ∧ b ≤ a}

@[simp] theorem mem_forwardConeIn_iff {P : FinitePatch (α := α)} {a b : α} :
    b ∈ forwardConeIn (α := α) P a ↔ b ∈ P.carrier ∧ a ≤ b :=
  Iff.rfl

@[simp] theorem mem_backwardConeIn_iff {P : FinitePatch (α := α)} {a b : α} :
    b ∈ backwardConeIn (α := α) P a ↔ b ∈ P.carrier ∧ b ≤ a :=
  Iff.rfl

 theorem incidence_of_mem_forwardConeIn
    (S : SpinNet α 𝕜 T D)
    {P : FinitePatch (α := α)} {a b : α}
    (ha : a ∈ P.carrier)
    (hb : b ∈ forwardConeIn (α := α) P a) :
    S.twistorIncidence.Incidence (S.dualAt a) (S.twistorAt b) := by
  exact incidence_of_le S hb.2

 theorem cone_point_of_patch_intersection
    (S : SpinNet α 𝕜 T D)
    {P : FinitePatch (α := α)} {a b : α}
    (hab : b ∈ forwardConeIn (α := α) P a)
    (hba : b ∈ backwardConeIn (α := α) P a) :
    b = a :=
  cones_intersect_self S a b hab.2 hba.2

/-- Event-labelled local states on a patch. -/
def localState (S : SpinNet α 𝕜 T D) (P : FinitePatch (α := α)) : Type _ :=
  Σ a : {a // a ∈ P.carrier}, S.stateDiagram.obj a.1

/-- Inclusion of patches transports local states by retaining the same event label. -/
def mapLocalState (S : SpinNet α 𝕜 T D) {P Q : FinitePatch (α := α)} (f : P ⟶ Q) :
    localState (α := α) S P → localState (α := α) S Q
  | ⟨a, x⟩ => ⟨⟨a.1, f.down a.2⟩, x⟩

@[simp] theorem mapLocalState_id (S : SpinNet α 𝕜 T D)
    (P : FinitePatch (α := α)) (x : localState (α := α) S P) :
    mapLocalState (α := α) S (𝟙 P) x = x := by
  cases x with
  | mk a x =>
      cases a with
      | mk a ha =>
          rfl

@[simp] theorem mapLocalState_comp (S : SpinNet α 𝕜 T D) {P Q R : FinitePatch (α := α)}
    (f : P ⟶ Q) (g : Q ⟶ R) (x : localState (α := α) S P) :
    mapLocalState (α := α) S (f ≫ g) x =
      mapLocalState (α := α) S g (mapLocalState (α := α) S f x) := by
  cases x with
  | mk a x =>
      cases a with
      | mk a ha =>
          rfl

/-- The patch-local-state assignment is a functor to `Type`. -/
def localStateFunctor (S : SpinNet α 𝕜 T D) : FinitePatch (α := α) ⥤ Type _ where
  obj P := localState (α := α) S P
  map f := mapLocalState (α := α) S f
  map_id := by
    intro P
    funext x
    exact mapLocalState_id (α := α) S P x
  map_comp := by
    intro P Q R f g
    funext x
    exact mapLocalState_comp (α := α) S f g x

section PatchCocones

variable {J : Type w} [Category J]

/-- An upper-bound patch for a patch diagram means every stage includes into it. -/
def PatchUpperBound (F : J ⥤ FinitePatch (α := α)) (apex : FinitePatch (α := α)) : Prop :=
  ∀ j, F.obj j ≤ apex

/-- Any upper-bound patch induces a cocone in the thin patch category. -/
def patchCoconeOfUpperBound
    (F : J ⥤ FinitePatch (α := α))
    {apex : FinitePatch (α := α)}
    (hub : PatchUpperBound (α := α) F apex) :
    Cocone F where
  pt := apex
  ι :=
    { app := fun j => PLift.up (hub j)
      naturality := by
        intro i j f
        apply Subsingleton.elim }

/-- Local states over a patch cocone are functorially reachable from every stage. -/
theorem localState_reaches_cocone
    (F : J ⥤ FinitePatch (α := α))
    {apex : FinitePatch (α := α)}
    (hub : PatchUpperBound (α := α) F apex)
    (j : J)
    (x : (localStateFunctor (α := α) S).obj (F.obj j)) :
    (localStateFunctor (α := α) S).map ((patchCoconeOfUpperBound (α := α) F hub).ι.app j) x =
      mapLocalState (α := α) S (PLift.up (hub j)) x :=
  rfl

end PatchCocones

end SpinNetPatches

end InfoGeometry.Canonical.FinitePenrosePatchCategory
