import Mathlib.Topology.Category.CompHaus.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentIndexedObservationRangeTopCat

/-!
# Compact indexed symbolic-latent observation ranges

The ambient coordinate carrier `ι → ℝ` is not compact in general, so the
compact-Hausdorff layer is kept on the observation ranges only.  This owner
packages compact latent carriers and transports indexed observation ranges in
`CompHaus`, without making an unjustified compactness claim about ambient
coordinates.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open TripotentFiveGradeMirrorTopological

noncomputable section

variable {ι : Type} [Fintype ι]

structure CompactIndexedSymbolicLatentSystemObject where
  carrier : CompHaus
  system : FiniteSymbolicLatentSystem carrier ι

structure CompactIndexedSymbolicLatentSystemHom
    (S T : CompactIndexedSymbolicLatentSystemObject (ι := ι)) where
  indexed : SymbolicLatentIndexedHomeomorph S.system T.system

namespace CompactIndexedSymbolicLatentSystemHom

def id (S : CompactIndexedSymbolicLatentSystemObject (ι := ι)) :
    CompactIndexedSymbolicLatentSystemHom S S where
  indexed := indexedHomeomorphId

def comp
    {S T U : CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (g : CompactIndexedSymbolicLatentSystemHom T U)
    (f : CompactIndexedSymbolicLatentSystemHom S T) :
    CompactIndexedSymbolicLatentSystemHom S U where
  indexed := indexedHomeomorphComp g.indexed f.indexed

@[ext] theorem ext
    {S T : CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (f g : CompactIndexedSymbolicLatentSystemHom S T)
    (h : f.indexed = g.indexed) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

end CompactIndexedSymbolicLatentSystemHom

instance compactIndexedSymbolicLatentSystemCategory :
    Category (CompactIndexedSymbolicLatentSystemObject (ι := ι)) where
  Hom S T := CompactIndexedSymbolicLatentSystemHom S T
  id := CompactIndexedSymbolicLatentSystemHom.id
  comp f g := CompactIndexedSymbolicLatentSystemHom.comp g f
  id_comp := by
    intro S T F
    apply CompactIndexedSymbolicLatentSystemHom.ext
    change indexedHomeomorphComp F.indexed indexedHomeomorphId = F.indexed
    exact indexedHomeomorphId_comp F.indexed
  comp_id := by
    intro S T F
    apply CompactIndexedSymbolicLatentSystemHom.ext
    change indexedHomeomorphComp indexedHomeomorphId F.indexed = F.indexed
    exact indexedHomeomorphComp_id F.indexed
  assoc := by
    intro R S T U f g h
    apply CompactIndexedSymbolicLatentSystemHom.ext
    rfl

noncomputable def compactIndexedObservationRangeCompHausFunctor :
    (CompactIndexedSymbolicLatentSystemObject (ι := ι)) ⥤ CompHaus where
  obj S := symbolicObservationRangeCompHaus S.system
  map F := (indexedObservationQuotientRangeCompHausIso F.indexed).inv
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro y
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro y
    rfl

theorem compactIndexedObservationRangeCompHausFunctor_map_apply
    {S T : CompactIndexedSymbolicLatentSystemObject (ι := ι)}
    (F : CompactIndexedSymbolicLatentSystemHom S T)
    (y : Set.range (symbolicObservationQuotientMap S.system)) :
    (compactIndexedObservationRangeCompHausFunctor.map F y).1 =
      indexedCoordinateAction (indexedHomeomorphSymm F.indexed) y.1 := by
  exact indexedObservationQuotientRangeCompHausIso_apply
    (indexedHomeomorphSymm F.indexed) y

end
end InfoGeometry.Topology
