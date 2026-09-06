import Mathlib
import InfoGeometry.MassSpectrometry.ChemicalGraph
import InfoGeometry.MassSpectrometry.FragmentationColimit

/-!
# Molecular fragment diagrams and their categorical colimit

A `MolecularFragmentDiagram` assigns a finite labelled molecular fragment to
every object of a fragmentation DAG and an exact molecular embedding to every
reachable causal arrow.  Coherence of the embedding functions turns the vertex
carriers into a genuine functor from the fragmentation preorder to `Type`.

The Mathlib colimit of that functor is therefore an honest categorical colimit
of the vertex carriers.  Exact atom preservation allows atom labels to descend
to the colimit.  Bonds are recorded by the symmetric union of all stage-bond
images.

This does not yet construct a categorical pushout/colimit in a dedicated
category of bond-labelled graphs; the universal property proved here is the
`Type` colimit of the coherent vertex diagram, with labels and bonds transported
on top of it.
-/

noncomputable section

namespace InfoGeometry.MassSpectrometry

open CategoryTheory

/-- Coherent finite molecular fragments indexed by a fragmentation DAG. -/
structure MolecularFragmentDiagram {n : ℕ} (D : FragmentationDAG n) where
  vertexCount : Fin n → ℕ
  graph : ∀ u, MolecularGraph (vertexCount u)
  map : ∀ {u v : Fin n}, D.Reach u v → (graph u).Embedding (graph v)
  map_refl : ∀ u,
    (map (Relation.ReflTransGen.refl : D.Reach u u)).toFun = id
  map_trans : ∀ {u v w} (huv : D.Reach u v) (hvw : D.Reach v w),
    (map (Relation.ReflTransGen.trans huv hvw)).toFun =
      (map hvw).toFun ∘ (map huv).toFun

namespace MolecularFragmentDiagram

variable {n : ℕ} {D : FragmentationDAG n}

/-- Forget labels and retain the coherent fragmentation-indexed vertex carriers. -/
def vertexDiagram (M : MolecularFragmentDiagram D) : FragmentVertexDiagram D where
  carrier := fun u => Fin (M.vertexCount u)
  map := fun h => (M.map h).toFun
  map_refl := M.map_refl
  map_trans := M.map_trans

/-- Categorical vertex colimit of all molecular fragments in the diagram. -/
noncomputable def VertexColimit (M : MolecularFragmentDiagram D) : Type :=
  M.vertexDiagram.carrierColimit

/-- Canonical injection of one molecular-fragment vertex carrier into the
colimit. -/
noncomputable def ι (M : MolecularFragmentDiagram D) (u : Fin n) :
    Fin (M.vertexCount u) → M.VertexColimit :=
  M.vertexDiagram.ι u

/-- Atom labels form a compatible cocone because every molecular embedding
preserves them exactly. -/
theorem atom_compatible (M : MolecularFragmentDiagram D)
    {u v : Fin n} (h : D.Reach u v) :
    (M.map h).toFun ≫ (M.graph v).atom = (M.graph u).atom := by
  ext i
  exact (M.map h).atom_preserving i

/-- Canonical atom label on the molecular fragmentation colimit. -/
noncomputable def atomLabel (M : MolecularFragmentDiagram D) :
    M.VertexColimit → AtomLabel :=
  M.vertexDiagram.descend (fun u => (M.graph u).atom) (by
    intro u v h
    exact M.atom_compatible h)

/-- The colimit label restricts to the original atom label at every
fragmentation stage. -/
theorem atomLabel_ι (M : MolecularFragmentDiagram D)
    (u : Fin n) :
    M.ι u ≫ M.atomLabel = (M.graph u).atom := by
  exact M.vertexDiagram.descend_ι
    (fun i => (M.graph i).atom)
    (by intro i j h; exact M.atom_compatible h) u

/-- Bond relation on the colimit: two reconstructed vertices are bonded when
they are images of a bonded pair in at least one fragment stage. -/
def Bonded (M : MolecularFragmentDiagram D)
    (x y : M.VertexColimit) : Prop :=
  ∃ u : Fin n, ∃ i j : Fin (M.vertexCount u),
    x = M.ι u i ∧ y = M.ι u j ∧ (M.graph u).Adj i j

/-- The induced colimit bond relation is symmetric. -/
theorem bonded_symm (M : MolecularFragmentDiagram D)
    {x y : M.VertexColimit} : M.Bonded x y → M.Bonded y x := by
  rintro ⟨u, i, j, hx, hy, hij⟩
  refine ⟨u, j, i, hy, hx, ?_⟩
  exact ((M.graph u).adj_symm).mpr hij

/-- Exact molecular embeddings along reachability preserve adjacency. -/
theorem map_adj_iff (M : MolecularFragmentDiagram D)
    {u v : Fin n} (h : D.Reach u v)
    {i j : Fin (M.vertexCount u)} :
    (M.graph v).Adj ((M.map h).toFun i) ((M.map h).toFun j) ↔
      (M.graph u).Adj i j := by
  exact (M.map h).adj_iff

/-- A bond in any stage yields a bond between its two canonical colimit images. -/
theorem bonded_of_stage_bond (M : MolecularFragmentDiagram D)
    (u : Fin n) {i j : Fin (M.vertexCount u)}
    (h : (M.graph u).Adj i j) :
    M.Bonded (M.ι u i) (M.ι u j) := by
  exact ⟨u, i, j, rfl, rfl, h⟩

end MolecularFragmentDiagram

end InfoGeometry.MassSpectrometry
