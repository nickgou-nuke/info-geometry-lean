import Mathlib

/-!
# Premonoidal Pentagon Defect

This file formalizes the `q`-defect of the Pentagon identity in a premonoidal setting, 
as inspired by Joyce's study of coherence. Instead of requiring a strict Pentagon 
for the associator $a$, we introduce an explicit natural automorphism $q$ that measures 
the failure of the Pentagon commuting diagram.

The geometry of the tensor product here differentiates between:
- Re-parenthesization (measured by $a$).
- The history/order of internal composition events (measured by $q$).

The standard monoidal regime corresponds exactly to $q = \mathrm{id}$.
-/

namespace InfoGeometry.Categorical.PremonoidalPentagonDefect

/--
A structural datum for the premonoidal Pentagon defect.
Instead of a strict `associator_pentagon` axiom, this provides the $a$ and $q$ morphisms.
We keep the category abstract to focus on the exact coherence structure.
-/
structure PremonoidalPentagonDefectDatum (Obj : Type*) where
  /-- Tensor product on objects. -/
  tensor : Obj → Obj → Obj
  
  /-- Formal hom-spaces for the coherence cells. -/
  Hom : Obj → Obj → Type*
  
  /-- Composition of coherence cells. -/
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  
  /-- Identity coherence cell. -/
  id : ∀ X : Obj, Hom X X

  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f

  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f

  comp_assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y)
    (h : Hom Y Z), comp (comp f g) h = comp f (comp g h)
  
  /-- The associator structural isomorphism: $(X \otimes Y) \otimes Z \to X \otimes (Y \otimes Z)$. -/
  a : ∀ X Y Z : Obj, Hom (tensor (tensor X Y) Z) (tensor X (tensor Y Z))
  
  /-- The $q$-defect structural automorphism. It measures the failure of the standard Pentagon. 
      It acts on the root of the Pentagon diagram: $((W \otimes X) \otimes Y) \otimes Z$. -/
  q : ∀ W X Y Z : Obj, Hom (tensor (tensor (tensor W X) Y) Z) (tensor (tensor (tensor W X) Y) Z)
  
  /-- Formal inverse of $a$. -/
  a_inv : ∀ X Y Z : Obj, Hom (tensor X (tensor Y Z)) (tensor (tensor X Y) Z)
  
  /-- $a$ and $a\_inv$ are inverses. -/
  a_comp_a_inv : ∀ X Y Z : Obj, comp (a X Y Z) (a_inv X Y Z) = id _
  a_inv_comp_a : ∀ X Y Z : Obj, comp (a_inv X Y Z) (a X Y Z) = id _

  /-- Functorial tensor product of morphisms (whiskering/parallel composition). -/
  tensorHom : ∀ {A B C D : Obj}, Hom A B → Hom C D → Hom (tensor A C) (tensor B D)
  
  /-- 
  The $q$-deformed Pentagon identity.
  Instead of the two paths being strictly equal, they differ exactly by $q$.
  
  Path 1 (short): $a \circ a$
  Path 2 (long):  $(\mathrm{id} \otimes a) \circ a \circ (a \otimes \mathrm{id})$
  
  Here we state it as: long_path = comp q short_path.
  -/
  q_pentagon : ∀ W X Y Z : Obj,
    comp (tensorHom (a W X Y) (id Z)) (comp (a W (tensor X Y) Z) (tensorHom (id W) (a X Y Z))) =
    comp (q W X Y Z) (comp (a (tensor W X) Y Z) (a W X (tensor Y Z)))

/-- 
The condition for reducing to the standard monoidal regime.
If $q$ is the identity, then the strict Pentagon is recovered.
-/
def IsMonoidalRegime {Obj : Type*} (D : PremonoidalPentagonDefectDatum Obj) : Prop :=
  ∀ W X Y Z : Obj, D.q W X Y Z = D.id (D.tensor (D.tensor (D.tensor W X) Y) Z)

theorem pentagon_of_isMonoidalRegime
    {Obj : Type*} (D : PremonoidalPentagonDefectDatum Obj)
    (hD : IsMonoidalRegime D)
    (W X Y Z : Obj) :
    D.comp (D.tensorHom (D.a W X Y) (D.id Z))
        (D.comp (D.a W (D.tensor X Y) Z)
          (D.tensorHom (D.id W) (D.a X Y Z))) =
      D.comp (D.a (D.tensor W X) Y Z)
        (D.a W X (D.tensor Y Z)) := by
  rw [D.q_pentagon W X Y Z, hD W X Y Z]
  rw [D.id_comp]

end InfoGeometry.Categorical.PremonoidalPentagonDefect
