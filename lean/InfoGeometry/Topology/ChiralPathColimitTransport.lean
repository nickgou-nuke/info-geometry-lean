import Mathlib
import InfoGeometry.Topology.ChiralDirectedGraphHomotopy

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits

/-!
# Native colimit transport for directed chiral path classes

This owner deliberately does not invent a particular tower of finite graphs.
Instead it records the exact input needed from such a tower: a native
`Type` diagram and a compatible cocone whose target is a fixed directed
path-class carrier.  Mathlib then supplies the induced map and its universal
property.
-/

variable {J : Type*} [Category J]
variable {G : ChiralDigraph} {u v : G.Vertex}

/-- A stagewise readout of a directed-path tower into one homotopy-class
carrier.  The compatibility equations are carried by the native cocone. -/
structure ChiralPathClassCocone (D : J ⥤ Type _) where
  ι : ∀ j, D.obj j → DirectedPathClass G u v
  naturality : ∀ {j k} (f : j ⟶ k), D.map f ≫ ι k = ι j

def ChiralPathClassCocone.toCocone
    {D : J ⥤ Type _}
    (c : ChiralPathClassCocone (G := G) (u := u) (v := v) D) : Cocone D where
  pt := DirectedPathClass G u v
  ι :=
    { app := c.ι
      naturality := by
        intro j k f
        simpa using c.naturality f }

/-- The canonical readout from a stage diagram to directed path classes. -/
noncomputable def chiralPathColimitReadout
    (D : J ⥤ Type _)
    (c : ChiralPathClassCocone (G := G) (u := u) (v := v) D)
    [HasColimit D]
    :
    colimit D ⟶ DirectedPathClass G u v := by
  exact colimit.desc D c.toCocone

theorem chiralPathColimitReadout_stage
    (D : J ⥤ Type _)
    (c : ChiralPathClassCocone (G := G) (u := u) (v := v) D)
    [HasColimit D]
    (j : J) :
    colimit.ι D j ≫ chiralPathColimitReadout D c = c.ι j := by
  exact colimit.ι_desc c.toCocone j

theorem chiralPathColimitReadout_unique
    (D : J ⥤ Type _)
    (c : ChiralPathClassCocone (G := G) (u := u) (v := v) D)
    [HasColimit D]
    {f g : colimit D ⟶ DirectedPathClass G u v}
    (h : ∀ j, colimit.ι D j ≫ f = colimit.ι D j ≫ g) :
    f = g := by
  apply colimit.hom_ext
  intro j
  exact h j

end InfoGeometry.Topology
