import Lean

namespace DAG

universe u v u' v' u'' v''

/--
A typed incidence system represented by subject-predicate-object triples.

This is the common skeleton behind RDF rows, Lean expression/binder incidence,
wire/gate incidence, categorical arrows, proof-step incidence, and derived
translation graphs.  The structure is intentionally minimal: extra typing,
binder, constant-policy, and kernel-checking constraints are layered on top.
-/
structure TripleSystem where
  Obj : Type u
  Rel : Type v
  triple : Obj → Rel → Obj → Prop

namespace TripleSystem

/-- A triple homomorphism preserves every valid incidence triple. -/
structure Hom (A : TripleSystem.{u, v}) (B : TripleSystem.{u', v'}) where
  mapObj : A.Obj → B.Obj
  mapRel : A.Rel → B.Rel
  preserves :
    ∀ {s p o : _}, A.triple s p o →
      B.triple (mapObj s) (mapRel p) (mapObj o)

namespace Hom

/-- Identity triple homomorphism. -/
def id (A : TripleSystem.{u, v}) : Hom A A where
  mapObj := fun x => x
  mapRel := fun r => r
  preserves := by
    intro s p o h
    exact h

/-- Composition of triple homomorphisms. -/
def comp
    {A : TripleSystem.{u, v}}
    {B : TripleSystem.{u', v'}}
    {C : TripleSystem.{u'', v''}}
    (G : Hom B C)
    (F : Hom A B) : Hom A C where
  mapObj := G.mapObj ∘ F.mapObj
  mapRel := G.mapRel ∘ F.mapRel
  preserves := by
    intro s p o h
    exact G.preserves (F.preserves h)

@[simp] theorem id_mapObj (A : TripleSystem) (x : A.Obj) :
    (id A).mapObj x = x := rfl

@[simp] theorem id_mapRel (A : TripleSystem) (r : A.Rel) :
    (id A).mapRel r = r := rfl

@[simp] theorem comp_mapObj
    {A : TripleSystem.{u, v}}
    {B : TripleSystem.{u', v'}}
    {C : TripleSystem.{u'', v''}}
    (G : Hom B C)
    (F : Hom A B)
    (x : A.Obj) :
    (comp G F).mapObj x = G.mapObj (F.mapObj x) := rfl

@[simp] theorem comp_mapRel
    {A : TripleSystem.{u, v}}
    {B : TripleSystem.{u', v'}}
    {C : TripleSystem.{u'', v''}}
    (G : Hom B C)
    (F : Hom A B)
    (r : A.Rel) :
    (comp G F).mapRel r = G.mapRel (F.mapRel r) := rfl

end Hom

/--
Bidirectional triple homomorphism.  Downstream SCC dedup classes should be
formed from verified directed homomorphism edges; this structure is the local
two-way version.
-/
structure BiHom (A : TripleSystem.{u, v}) (B : TripleSystem.{u', v'}) where
  forward : Hom A B
  backward : Hom B A

namespace BiHom

def refl (A : TripleSystem.{u, v}) : BiHom A A where
  forward := Hom.id A
  backward := Hom.id A

def symm {A : TripleSystem.{u, v}} {B : TripleSystem.{u', v'}} (H : BiHom A B) :
    BiHom B A where
  forward := H.backward
  backward := H.forward

end BiHom

end TripleSystem

end DAG
