import InfoGeometry.Topology.SymbolicLatentIndexedObservationRangeTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Functorial indexed symbolic-latent observation ranges

An indexed equivalence may permute the finite observation coordinates.  Its
quotient-range homeomorphism is contravariant when written as the raw
`Homeomorph` supplied by the transport owner.  This file packages the
inverse direction as a covariant `TopCat` functor.
-/

namespace InfoGeometry.Topology

open CategoryTheory
open TripotentFiveGradeMirrorTopological

noncomputable section

structure IndexedSymbolicLatentSystemObject (ι : Type) [Fintype ι] where
  carrier : TopCat
  system : FiniteSymbolicLatentSystem carrier ι

structure IndexedSymbolicLatentSystemHom
    {ι : Type} [Fintype ι]
    (S T : IndexedSymbolicLatentSystemObject ι) where
  indexed : SymbolicLatentIndexedHomeomorph S.system T.system

namespace IndexedSymbolicLatentSystemHom

variable {ι : Type} [Fintype ι]

def id (S : IndexedSymbolicLatentSystemObject ι) :
    IndexedSymbolicLatentSystemHom S S where
  indexed := indexedHomeomorphId

def comp
    {S T U : IndexedSymbolicLatentSystemObject ι}
    (g : IndexedSymbolicLatentSystemHom T U)
    (f : IndexedSymbolicLatentSystemHom S T) :
    IndexedSymbolicLatentSystemHom S U where
  indexed := indexedHomeomorphComp g.indexed f.indexed

@[ext] theorem ext
    {S T : IndexedSymbolicLatentSystemObject ι}
    (f g : IndexedSymbolicLatentSystemHom S T)
    (h : f.indexed = g.indexed) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

end IndexedSymbolicLatentSystemHom

instance indexedSymbolicLatentSystemCategory (ι : Type) [Fintype ι] :
    Category (IndexedSymbolicLatentSystemObject ι) where
  Hom S T := IndexedSymbolicLatentSystemHom S T
  id := IndexedSymbolicLatentSystemHom.id
  comp := fun {S T U} f g => IndexedSymbolicLatentSystemHom.comp g f
  id_comp := by
    intro S T F
    apply IndexedSymbolicLatentSystemHom.ext
    exact indexedHomeomorphComp_id F.indexed
  comp_id := by
    intro S T F
    apply IndexedSymbolicLatentSystemHom.ext
    exact indexedHomeomorphId_comp F.indexed
  assoc := by
    intro R S T U h g f
    apply IndexedSymbolicLatentSystemHom.ext
    rfl

noncomputable def indexedSymbolicLatentObservationRangeFunctor
    (ι : Type) [Fintype ι] :
    (IndexedSymbolicLatentSystemObject ι) ⥤ TopCat where
  obj S := TopCat.of (Set.range (symbolicObservationQuotientMap S.system))
  map F :=
    (indexedObservationQuotientRangeTopCatIso F.indexed).inv
  map_id S := by
    apply TopCat.hom_ext
    ext y
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    ext y
    rfl

theorem indexedSymbolicLatentObservationRangeFunctor_map_apply
    {ι : Type} [Fintype ι]
    {S T : IndexedSymbolicLatentSystemObject ι}
    (F : IndexedSymbolicLatentSystemHom S T)
    (y : Set.range (symbolicObservationQuotientMap S.system)) :
    (indexedSymbolicLatentObservationRangeFunctor ι).map F y =
      (indexedQuotientRangeHomeomorph F.indexed).symm y := rfl

end

end InfoGeometry.Topology
