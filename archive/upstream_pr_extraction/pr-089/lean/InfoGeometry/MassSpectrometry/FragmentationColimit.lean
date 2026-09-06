import Mathlib
import InfoGeometry.MassSpectrometry.FragmentationPosetCategory

/-!
# Fragmentation-indexed categorical colimits

This file closes the generic categorical layer over a fragmentation DAG.
Reachability supplies the preorder category; a `FragmentVertexDiagram` supplies
carriers and coherent maps along reachable fragmentation paths; Mathlib then
constructs the ordinary categorical colimit in `Type`.

This is a genuine colimit theorem for the supplied diagram.  It does not say
that an arbitrary molecular graph is recovered from spectra: chemistry-specific
labels and bonds require the additional compatibility data provided by
`ChemicalGraph` / `FragmentationPushout`.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open CategoryTheory CategoryTheory.Limits

/-- A coherent family of vertex carriers transported along fragmentation
reachability. -/
structure FragmentVertexDiagram {n : ℕ} (D : FragmentationDAG n) where
  carrier : Fin n → Type
  map : ∀ {u v : Fin n}, D.Reach u v → carrier u → carrier v
  map_refl : ∀ u, map (Relation.ReflTransGen.refl : D.Reach u u) = id
  map_trans : ∀ {u v w} (huv : D.Reach u v) (hvw : D.Reach v w),
    map (Relation.ReflTransGen.trans huv hvw) = map hvw ∘ map huv

namespace FragmentVertexDiagram

variable {n : ℕ} {D : FragmentationDAG n}

/-- The coherent reachability data is exactly a functor from the fragmentation
preorder category to `Type`. -/
noncomputable def toFunctor (V : FragmentVertexDiagram D) :
    letI : Preorder (Fin n) := D.reachPreorder
    Fin n ⥤ Type := by
  letI : Preorder (Fin n) := D.reachPreorder
  refine
    { obj := fun u => V.carrier u
      map := fun {u v} f => V.map (leOfHom f)
      map_id := ?_
      map_comp := ?_ }
  · intro u
    funext x
    have h := congrFun (V.map_refl u) x
    simpa using h
  · intro u v w f g
    funext x
    have h := congrFun (V.map_trans (leOfHom f) (leOfHom g)) x
    simpa [Function.comp_apply] using h

/-- Ordinary categorical colimit of the fragmentation-indexed carriers. -/
noncomputable def carrierColimit (V : FragmentVertexDiagram D) : Type :=
  letI : Preorder (Fin n) := D.reachPreorder
  colimit V.toFunctor

/-- Canonical injection of a fragment carrier into the fragmentation colimit. -/
noncomputable def ι (V : FragmentVertexDiagram D) (u : Fin n) :
    V.carrier u → V.carrierColimit := by
  letI : Preorder (Fin n) := D.reachPreorder
  exact colimit.ι V.toFunctor u

/-- Colimit injections commute with every reachable fragmentation map. -/
theorem ι_naturality (V : FragmentVertexDiagram D)
    {u v : Fin n} (h : D.Reach u v) :
    V.map h ≫ V.ι v = V.ι u := by
  letI : Preorder (Fin n) := D.reachPreorder
  let f : u ⟶ v := homOfLE h
  simpa [FragmentVertexDiagram.ι, f] using
    (colimit.w V.toFunctor f)

/-- Universal map out of the fragmentation colimit from a cocone-compatible
family of functions. -/
noncomputable def descend (V : FragmentVertexDiagram D)
    {X : Type} (k : ∀ u, V.carrier u → X)
    (hk : ∀ {u v} (h : D.Reach u v), V.map h ≫ k v = k u) :
    V.carrierColimit → X := by
  letI : Preorder (Fin n) := D.reachPreorder
  let t : Cocone V.toFunctor :=
    { pt := X
      ι :=
        { app := fun u => k u
          naturality := by
            intro u v f
            simpa using hk (leOfHom f) } }
  exact colimit.desc V.toFunctor t

/-- The universal descent map agrees with the supplied map on every fragment
carrier. -/
theorem descend_ι (V : FragmentVertexDiagram D)
    {X : Type} (k : ∀ u, V.carrier u → X)
    (hk : ∀ {u v} (h : D.Reach u v), V.map h ≫ k v = k u)
    (u : Fin n) :
    V.ι u ≫ V.descend k hk = k u := by
  letI : Preorder (Fin n) := D.reachPreorder
  let t : Cocone V.toFunctor :=
    { pt := X
      ι :=
        { app := fun i => k i
          naturality := by
            intro i j f
            simpa using hk (leOfHom f) } }
  simpa [FragmentVertexDiagram.ι, FragmentVertexDiagram.descend, t] using
    (colimit.ι_desc t u)

end FragmentVertexDiagram

end InfoGeometry.MassSpectrometry
