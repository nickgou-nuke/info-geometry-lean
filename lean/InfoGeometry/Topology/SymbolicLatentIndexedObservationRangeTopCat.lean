import InfoGeometry.Topology.TripotentFiveGradeMirrorTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Indexed symbolic-latent observation transport

The ordinary symbolic-latent morphism keeps the observable index fixed.
Symmetries such as a grade mirror or a colour permutation also permute the
index set.  This owner supplies the corresponding coordinate action and the
induced homeomorphism on raw observation ranges.
-/

namespace InfoGeometry.Topology

open TripotentFiveGradeMirrorTopological
open CategoryTheory

noncomputable section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type*} [Fintype ι]

def indexedHomeomorphId
    {S : FiniteSymbolicLatentSystem X ι} :
    SymbolicLatentIndexedHomeomorph S S where
  latent := Homeomorph.refl X
  index := Equiv.refl ι
  intertwines := by
    intro i x
    rfl

def indexedHomeomorphComp
    {Z : Type*} [TopologicalSpace Z]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (G : SymbolicLatentIndexedHomeomorph T U)
    (F : SymbolicLatentIndexedHomeomorph S T) :
    SymbolicLatentIndexedHomeomorph S U where
  latent := F.latent.trans G.latent
  index := F.index.trans G.index
  intertwines := by
    intro i x
    rw [Homeomorph.trans_apply, Equiv.trans_apply]
    rw [G.intertwines (F.index i) (F.latent x)]
    exact F.intertwines i x

def indexedHomeomorphSymm
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    SymbolicLatentIndexedHomeomorph T S where
  latent := F.latent.symm
  index := F.index.symm
  intertwines := by
    intro i y
    simpa using
      (F.intertwines (F.index.symm i) (F.latent.symm y)).symm

theorem indexedHomeomorph_ext
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {F G : SymbolicLatentIndexedHomeomorph S T}
    (hLatent : F.latent = G.latent)
    (hIndex : F.index = G.index) :
    F = G := by
  cases F
  cases G
  cases hLatent
  cases hIndex
  rfl

@[simp] theorem indexedHomeomorphComp_id
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    indexedHomeomorphComp
        (indexedHomeomorphId (S := T)) F = F := by
  apply indexedHomeomorph_ext
  · ext x
    rfl
  · ext i
    rfl

@[simp] theorem indexedHomeomorphId_comp
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    indexedHomeomorphComp F
        (indexedHomeomorphId (S := S)) = F := by
  apply indexedHomeomorph_ext
  · ext x
    rfl
  · ext i
    rfl

@[simp] theorem indexedHomeomorphComp_symm
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    indexedHomeomorphComp (indexedHomeomorphSymm F) F =
      indexedHomeomorphId (S := S) := by
  apply indexedHomeomorph_ext
  · ext x
    change F.latent.symm (F.latent x) = x
    exact F.latent.symm_apply_apply x
  · ext i
    change F.index.symm (F.index i) = i
    exact F.index.symm_apply_apply i

@[simp] theorem indexedHomeomorphSymm_comp
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    indexedHomeomorphComp F (indexedHomeomorphSymm F) =
      indexedHomeomorphId (S := T) := by
  apply indexedHomeomorph_ext
  · ext x
    change F.latent (F.latent.symm x) = x
    exact F.latent.apply_symm_apply x
  · ext i
    change F.index (F.index.symm i) = i
    exact F.index.apply_symm_apply i

def indexedCoordinateAction
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T)
    (v : ι → ℝ) : ι → ℝ :=
  fun i => v (F.index i)

def indexedCoordinateActionHomeomorph
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    (ι → ℝ) ≃ₜ (ι → ℝ) where
  toEquiv :=
    { toFun := indexedCoordinateAction F
      invFun := fun v i => v (F.index.symm i)
      left_inv := by
        intro v
        funext i
        simp [indexedCoordinateAction]
      right_inv := by
        intro v
        funext i
        simp [indexedCoordinateAction] }
  continuous_toFun := by
    unfold indexedCoordinateAction
    exact continuous_pi (fun i => continuous_apply (F.index i))
  continuous_invFun := by
    exact continuous_pi (fun i => continuous_apply (F.index.symm i))

theorem indexedCoordinateAction_observationMap
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) (x : X) :
    indexedCoordinateAction F
        (symbolicObservationMap T (F.latent x)) =
      symbolicObservationMap S x := by
  funext i
  exact F.intertwines i x

noncomputable def indexedObservationRangeHomeomorph
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    Set.range (symbolicObservationMap T) ≃ₜ
      Set.range (symbolicObservationMap S) :=
  indexedCoordinateActionHomeomorph F |>.subtype (by
    intro v
    constructor
    · intro hv
      rcases hv with ⟨y, rfl⟩
      refine ⟨F.latent.symm y, ?_⟩
      simpa using
        (indexedCoordinateAction_observationMap F (F.latent.symm y)).symm
    · intro hv
      rcases hv with ⟨x, hx⟩
      refine ⟨F.latent x, ?_⟩
      apply (indexedCoordinateActionHomeomorph F).injective
      change indexedCoordinateAction F
          (symbolicObservationMap T (F.latent x)) =
        indexedCoordinateAction F v
      rw [indexedCoordinateAction_observationMap F x]
      exact hx)

theorem indexedObservationRangeHomeomorph_apply
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T)
    (y : Set.range (symbolicObservationMap T)) :
    (indexedObservationRangeHomeomorph F y).1 =
      indexedCoordinateAction F y.1 := rfl

noncomputable def indexedQuotientRangeHomeomorph
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    Set.range (symbolicObservationQuotientMap T) ≃ₜ
      Set.range (symbolicObservationQuotientMap S) :=
  indexedCoordinateActionHomeomorph F |>.subtype (by
    intro v
    constructor
    · intro hv
      rcases hv with ⟨q, rfl⟩
      refine _root_.Quotient.inductionOn q ?_
      intro y
      refine ⟨_root_.Quotient.mk (symbolicObservationalSetoid S)
          (F.latent.symm y), ?_⟩
      simpa using
        (indexedCoordinateAction_observationMap F (F.latent.symm y)).symm
    · intro hv
      rcases hv with ⟨q, hq⟩
      revert hq
      refine _root_.Quotient.inductionOn q ?_
      intro x hq
      refine ⟨_root_.Quotient.mk (symbolicObservationalSetoid T)
          (F.latent x), ?_⟩
      apply (indexedCoordinateActionHomeomorph F).injective
      change indexedCoordinateAction F
          (symbolicObservationQuotientMap T
            (_root_.Quotient.mk (symbolicObservationalSetoid T)
              (F.latent x))) =
        indexedCoordinateAction F v
      rw [symbolicObservationQuotientMap_mk]
      change indexedCoordinateAction F
          (symbolicObservationMap T (F.latent x)) =
        indexedCoordinateAction F v
      rw [indexedCoordinateAction_observationMap F x]
      change symbolicObservationMap S x = indexedCoordinateAction F v at hq
      exact hq)

theorem indexedQuotientRangeHomeomorph_apply
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T)
    (y : Set.range (symbolicObservationQuotientMap T)) :
    (indexedQuotientRangeHomeomorph F y).1 =
      indexedCoordinateAction F y.1 := rfl

theorem indexedQuotientRangeHomeomorph_comp
    {Z : Type*} [TopologicalSpace Z]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (G : SymbolicLatentIndexedHomeomorph T U)
    (F : SymbolicLatentIndexedHomeomorph S T) :
    indexedQuotientRangeHomeomorph (indexedHomeomorphComp G F) =
      (indexedQuotientRangeHomeomorph G).trans
        (indexedQuotientRangeHomeomorph F) := by
  ext y
  rfl

theorem indexedQuotientRangeHomeomorph_symm
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    indexedQuotientRangeHomeomorph (indexedHomeomorphSymm F) =
      (indexedQuotientRangeHomeomorph F).symm := by
  ext y
  rfl

noncomputable def indexedObservationQuotientRangeCompHausIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    symbolicObservationRangeCompHaus T ≅
      symbolicObservationRangeCompHaus S := by
  let e := indexedQuotientRangeHomeomorph F
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e.symm (e y) = y
        exact e.symm_apply_apply y
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro x
        change e (e.symm x) = x
        exact e.apply_symm_apply x }

theorem indexedObservationQuotientRangeCompHausIso_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T)
    (y : Set.range (symbolicObservationQuotientMap T)) :
    ((indexedObservationQuotientRangeCompHausIso F).hom y).1 =
      indexedCoordinateAction F y.1 := rfl

theorem indexedObservationQuotientRangeCompHausIso_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {ι : Type}
    [Fintype ι]
    [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    {U : FiniteSymbolicLatentSystem Z ι}
    (G : SymbolicLatentIndexedHomeomorph T U)
    (F : SymbolicLatentIndexedHomeomorph S T) :
    (indexedObservationQuotientRangeCompHausIso
        (indexedHomeomorphComp G F)).hom =
      (indexedObservationQuotientRangeCompHausIso G).hom ≫
        (indexedObservationQuotientRangeCompHausIso F).hom := by
  apply ConcreteCategory.hom_ext
  intro y
  change indexedQuotientRangeHomeomorph (indexedHomeomorphComp G F) y =
    indexedQuotientRangeHomeomorph F
      (indexedQuotientRangeHomeomorph G y)
  rw [indexedQuotientRangeHomeomorph_comp]
  rfl

noncomputable def indexedObservationQuotientRangeTopCatIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T) :
    TopCat.of (Set.range (symbolicObservationQuotientMap T)) ≅
      TopCat.of (Set.range (symbolicObservationQuotientMap S)) := by
  exact TopCat.isoOfHomeo (indexedQuotientRangeHomeomorph F)

theorem indexedObservationQuotientRangeTopCatIso_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {S : FiniteSymbolicLatentSystem X ι}
    {T : FiniteSymbolicLatentSystem Y ι}
    (F : SymbolicLatentIndexedHomeomorph S T)
    (y : Set.range (symbolicObservationQuotientMap T)) :
    ((indexedObservationQuotientRangeTopCatIso F).hom y).1 =
      indexedCoordinateAction F y.1 := rfl

end

end InfoGeometry.Topology
