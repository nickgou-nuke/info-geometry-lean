import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.MassSpectrometry.ChemicalGraph
import InfoGeometry.MassSpectrometry.MolecularFragmentColimit

/-!
# Category of finite labelled molecular graphs

Objects are finite `MolecularGraph`s and morphisms are the exact embeddings
already owned by `ChemicalGraph`.  This module closes the categorical carrier
that was previously implicit.

The resulting category is intentionally modest: no claim is made that it has
all pushouts or colimits.  A `MolecularFragmentDiagram` does however define a
functor from the fragmentation reachability preorder into this category, and
forgetting labels/bonds recovers the same vertex maps used by the existing
`FragmentationColimit` construction.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open CategoryTheory

/-- A finite molecular graph packaged with its vertex cardinality. -/
structure MolecularGraphObj where
  vertexCount : ℕ
  graph : MolecularGraph vertexCount

namespace MolecularGraphObj

/-- Exact molecular embedding as a categorical morphism. -/
structure Hom (X Y : MolecularGraphObj) where
  toEmbedding : X.graph.Embedding Y.graph

namespace Hom

@[ext] theorem ext {X Y : MolecularGraphObj} {f g : Hom X Y}
    (h : f.toEmbedding.toFun = g.toEmbedding.toFun) : f = g := by
  cases f with
  | mk fe =>
    cases g with
    | mk ge =>
      cases fe with
      | mk ff fi fa fb =>
        cases ge with
        | mk gf gi ga gb =>
          dsimp at h
          cases h
          rfl

end Hom

instance : Category MolecularGraphObj where
  Hom := Hom
  id X := ⟨MolecularGraph.Embedding.id X.graph⟩
  comp f g := ⟨f.toEmbedding.comp g.toEmbedding⟩
  id_comp := by
    intro X Y f
    apply Hom.ext
    funext i
    rfl
  comp_id := by
    intro X Y f
    apply Hom.ext
    funext i
    rfl
  assoc := by
    intro W X Y Z f g h
    apply Hom.ext
    funext i
    rfl

/-- Forget a labelled molecular graph to its finite vertex carrier. -/
def forgetVertices : MolecularGraphObj ⥤ Type where
  obj X := Fin X.vertexCount
  map f := f.toEmbedding.toFun
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

@[simp] theorem forgetVertices_obj (X : MolecularGraphObj) :
    forgetVertices.obj X = Fin X.vertexCount := rfl

@[simp] theorem forgetVertices_map {X Y : MolecularGraphObj} (f : X ⟶ Y) :
    forgetVertices.map f = f.toEmbedding.toFun := rfl

end MolecularGraphObj

namespace MolecularFragmentDiagram

variable {n : ℕ} {D : FragmentationDAG n}

/-- Package each stage of a molecular-fragment diagram as a categorical object. -/
def graphObject (M : MolecularFragmentDiagram D) (u : Fin n) : MolecularGraphObj where
  vertexCount := M.vertexCount u
  graph := M.graph u

/-- The coherent exact embeddings form a genuine functor from the
fragmentation reachability preorder to the molecular-graph category. -/
noncomputable def toGraphFunctor (M : MolecularFragmentDiagram D) :
    letI : Preorder (Fin n) := D.reachPreorder
    Fin n ⥤ MolecularGraphObj := by
  letI : Preorder (Fin n) := D.reachPreorder
  refine
    { obj := fun u => M.graphObject u
      map := fun {u v} f => ⟨M.map (leOfHom f)⟩
      map_id := ?_
      map_comp := ?_ }
  · intro u
    apply MolecularGraphObj.Hom.ext
    exact M.map_refl u
  · intro u v w f g
    apply MolecularGraphObj.Hom.ext
    exact M.map_trans (leOfHom f) (leOfHom g)

/-- After forgetting atom/bond structure, the graph functor has exactly the
same stage carrier as the existing vertex diagram. -/
theorem forgetGraphFunctor_obj (M : MolecularFragmentDiagram D) (u : Fin n) :
    letI : Preorder (Fin n) := D.reachPreorder
    (M.toGraphFunctor ⋙ MolecularGraphObj.forgetVertices).obj u =
      M.vertexDiagram.toFunctor.obj u := by
  letI : Preorder (Fin n) := D.reachPreorder
  rfl

/-- After forgetting atom/bond structure, every categorical molecular
embedding is exactly the vertex map used by `FragmentVertexDiagram`. -/
theorem forgetGraphFunctor_map (M : MolecularFragmentDiagram D)
    {u v : Fin n} (h : D.Reach u v) :
    letI : Preorder (Fin n) := D.reachPreorder
    (M.toGraphFunctor ⋙ MolecularGraphObj.forgetVertices).map (homOfLE h) =
      M.vertexDiagram.toFunctor.map (homOfLE h) := by
  letI : Preorder (Fin n) := D.reachPreorder
  rfl

end MolecularFragmentDiagram

end InfoGeometry.MassSpectrometry
