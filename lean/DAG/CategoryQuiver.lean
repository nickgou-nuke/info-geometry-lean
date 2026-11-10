import DAG.Basic
import DAG.ExactMorphism
import DAG.CategoryBridge
import Mathlib.CategoryTheory.Category.Basic

open Lean Meta
open CategoryTheory
open DAG

namespace DAG.CategoryQuiver

structure CategoryQuiverMorphism where
  entry : MorphismEntry
  dom   : HeadObj
  cod   : HeadObj
  domOK : entry.domHead = dom.head
  codOK : entry.codHead = cod.head

abbrev Hom (A B : HeadObj) := { m : CategoryQuiverMorphism // m.dom = A ∧ m.cod = B }

def mkHom (m : CategoryQuiverMorphism) : Hom m.dom m.cod :=
  ⟨m, rfl, rfl⟩

def idMorphism? (obj : HeadObj) (morphs : Array MorphismEntry) : MetaM (Option (Hom obj obj)) := do
  for m in morphs do
    if hdom : m.domHead = obj.head then
      if hcod : m.codHead = obj.head then
        let isId ← isDefinitionalIdentity m
        if isId then
          let qm : CategoryQuiverMorphism :=
            { entry := m, dom := obj, cod := obj, domOK := hdom, codOK := hcod }
          return some (mkHom qm)
  return none

def composeMorphism?
    {A B C : HeadObj}
    (f : Hom A B)
    (g : Hom B C)
    (morphs : Array MorphismEntry) :
    MetaM (Option (Hom A C)) := do
  for h in morphs do
    if hdom : h.domHead = A.head then
      if hcod : h.codHead = C.head then
        let isComp ← isCompositionExact f.1.entry g.1.entry h
        if isComp then
          let qm : CategoryQuiverMorphism :=
            { entry := h, dom := A, cod := C, domOK := hdom, codOK := hcod }
          return some (mkHom qm)
  return none

structure VerifiedCategoryData where
  id : ∀ A : HeadObj, Hom A A
  comp : ∀ {A B C : HeadObj}, Hom A B → Hom B C → Hom A C
  id_comp : ∀ {A B : HeadObj} (f : Hom A B), comp (id A) f = f
  comp_id : ∀ {A B : HeadObj} (f : Hom A B), comp f (id B) = f
  assoc :
    ∀ {A B C D : HeadObj} (f : Hom A B) (g : Hom B C) (h : Hom C D),
      comp (comp f g) h = comp f (comp g h)

noncomputable def ofVerifiedData (D : VerifiedCategoryData) : Category HeadObj where
  Hom A B := Hom A B
  id := D.id
  comp := fun f g => D.comp f g
  id_comp := D.id_comp
  comp_id := D.comp_id
  assoc := D.assoc

/-- Associativity in the conditional category data also identifies the
underlying harvested morphism metadata, after forgetting the endpoint subtype. -/
theorem VerifiedCategoryData.comp_assoc_entry (D : VerifiedCategoryData)
    {A B C E : HeadObj} (f : Hom A B) (g : Hom B C) (h : Hom C E) :
    ((D.comp (D.comp f g) h).1.entry) =
      ((D.comp f (D.comp g h)).1.entry) := by
  exact congrArg (fun m : Hom A E => m.1.entry) (D.assoc f g h)

def hasVerifiedIdentity (obj : HeadObj) (morphs : Array MorphismEntry) : MetaM Bool := do
  return (← idMorphism? obj morphs).isSome

def hasVerifiedComposition
    {A B C : HeadObj}
    (f : Hom A B)
    (g : Hom B C)
    (morphs : Array MorphismEntry) :
    MetaM Bool := do
  return (← composeMorphism? f g morphs).isSome

def countVerifiedIdentities (morphs : Array MorphismEntry) : MetaM ℕ := do
  let objSet := morphs.foldl (init := ({} : Std.HashSet Name)) fun acc m =>
    acc.insert m.domHead |>.insert m.codHead
  let mut count := 0
  for headName in objSet do
    let obj : HeadObj := ⟨headName⟩
    if ← hasVerifiedIdentity obj morphs then
      count := count + 1
  return count

def countVerifiedCompositions (morphs : Array MorphismEntry) : MetaM ℕ := do
  let mut byDom : Std.HashMap Name (Array CategoryQuiverMorphism) := {}
  for m in morphs do
    let domObj : HeadObj := ⟨m.domHead⟩
    let codObj : HeadObj := ⟨m.codHead⟩
    let bundled : CategoryQuiverMorphism :=
      { entry := m, dom := domObj, cod := codObj, domOK := rfl, codOK := rfl }
    byDom := byDom.insert m.domHead (byDom.getD m.domHead #[] |>.push bundled)
  let mut count := 0
  for (_, domMorphs) in byDom do
    for f0 in domMorphs do
      let f : Hom f0.dom f0.cod := mkHom f0
      if let some gCandidates := byDom.get? f0.cod.head then
        for g0 in gCandidates do
          if hfg : f0.cod = g0.dom then
            let g : Hom f0.cod g0.cod := ⟨g0, hfg.symm, rfl⟩
            if ← hasVerifiedComposition f g morphs then
              count := count + 1
  return count

end DAG.CategoryQuiver
