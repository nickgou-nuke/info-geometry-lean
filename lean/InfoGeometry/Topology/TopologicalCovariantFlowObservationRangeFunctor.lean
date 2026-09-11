import InfoGeometry.Topology.TopologicalCovariantFlowCompHausCategory
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationQuotientCompHaus

/-!
# Observation-range functor and readout naturality

The fixed-carrier flow category acts on the operator-valued observation range
through the explicit continuous operator automorphism carried by a morphism.
The latent readout is then a natural transformation from the latent carrier
functor to this range functor.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

variable {S : NoncommutativeObservableSystem X A ι}

def operatorObservationActionOfMorphism
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) (y : ι → A) : ι → A :=
  fun i => f.operatorMap (y i)

theorem continuous_operatorObservationActionOfMorphism
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) :
    Continuous (operatorObservationActionOfMorphism f) := by
  unfold operatorObservationActionOfMorphism
  apply continuous_pi
  intro i
  exact f.operatorMap_continuous.comp (continuous_apply i)

noncomputable def operatorObservationRangeMapOfMorphism
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) :
    Set.range S.operatorObservationMap → Set.range S.operatorObservationMap :=
  fun y =>
    ⟨operatorObservationActionOfMorphism f y.1, by
      rcases y with ⟨y, ⟨x, hx⟩⟩
      refine ⟨f.latentMap x, ?_⟩
      change S.operatorObservationMap (f.latentMap x) =
        operatorObservationActionOfMorphism f y
      rw [← hx]
      funext i
      exact f.observation_natural x i⟩

theorem continuous_operatorObservationRangeMapOfMorphism
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) :
    Continuous (operatorObservationRangeMapOfMorphism f) := by
  apply Continuous.subtype_mk
  exact continuous_operatorObservationActionOfMorphism f |>.comp
    continuous_subtype_val

noncomputable def operatorObservationRangeCompHausHomOfMorphism
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) :
    operatorObservationRangeCompHaus S ⟶ operatorObservationRangeCompHaus S := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  change CompHaus.of (Set.range S.operatorObservationMap) ⟶
    CompHaus.of (Set.range S.operatorObservationMap)
  exact ⟨TopCat.ofHom
    { toFun := operatorObservationRangeMapOfMorphism f
      continuous_toFun := continuous_operatorObservationRangeMapOfMorphism f }⟩

@[simp] theorem operatorObservationRangeCompHausHomOfMorphism_apply
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) (y : Set.range S.operatorObservationMap) :
    operatorObservationRangeCompHausHomOfMorphism f y =
      operatorObservationRangeMapOfMorphism f y := by
  change operatorObservationRangeMapOfMorphism f y =
    operatorObservationRangeMapOfMorphism f y
  rfl

theorem operatorObservationRangeCompHausHomOfMorphism_forget
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) :
    compHausToTop.map (operatorObservationRangeCompHausHomOfMorphism f) =
      TopCat.ofHom
        { toFun := operatorObservationRangeMapOfMorphism f
          continuous_toFun := continuous_operatorObservationRangeMapOfMorphism f } := by
  apply TopCat.hom_ext
  ext y
  rfl

noncomputable def operatorObservationRangeCompHausFunctor :
    NoncommutativeObservableTopologicalCovariantFlow S ⥤ CompHaus where
  obj _ := operatorObservationRangeCompHaus S
  map f := operatorObservationRangeCompHausHomOfMorphism f
  map_id := by
    intro F
    apply (compHausToTop).map_injective
    rw [operatorObservationRangeCompHausHomOfMorphism_forget]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    change operatorObservationRangeMapOfMorphism
        (TopologicalCovariantFlowMorphism.id F) y = y
    rfl
  map_comp f g := by
    apply (compHausToTop).map_injective
    rw [Functor.map_comp,
      operatorObservationRangeCompHausHomOfMorphism_forget,
      operatorObservationRangeCompHausHomOfMorphism_forget]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    change operatorObservationRangeMapOfMorphism
        (TopologicalCovariantFlowMorphism.comp f g) y =
      operatorObservationRangeMapOfMorphism g
        (operatorObservationRangeMapOfMorphism f y)
    rfl

noncomputable def operatorObservationCompHausReadoutHom
    (S : NoncommutativeObservableSystem X A ι) :
    CompHaus.of X ⟶ operatorObservationRangeCompHaus S := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  change CompHaus.of X ⟶ CompHaus.of (Set.range S.operatorObservationMap)
  exact ⟨TopCat.ofHom
    { toFun := fun x => ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩
      continuous_toFun :=
        (continuous_operatorObservationMap S).subtype_mk (fun x => ⟨x, rfl⟩) }⟩

@[simp] theorem operatorObservationCompHausReadoutHom_apply
    (S : NoncommutativeObservableSystem X A ι) (x : X) :
    operatorObservationCompHausReadoutHom S x =
      ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩ := by
  change (⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩ :
    Set.range S.operatorObservationMap) =
    ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩
  rfl

theorem operatorObservationCompHausReadoutHom_forget
    (S : NoncommutativeObservableSystem X A ι) :
    compHausToTop.map (operatorObservationCompHausReadoutHom S) =
      TopCat.ofHom
        { toFun := fun x => ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩
          continuous_toFun :=
            (continuous_operatorObservationMap S).subtype_mk
              (fun x => ⟨x, rfl⟩) } := by
  apply TopCat.hom_ext
  ext x
  rfl

noncomputable def operatorObservationCompHausReadoutNatTrans :
    (latentSpaceForgetfulCompHausFunctor (S := S)) ⟶
      (operatorObservationRangeCompHausFunctor (S := S)) where
  app F := operatorObservationCompHausReadoutHom S
  naturality := by
    intro F G f
    apply (compHausToTop).map_injective
    rw [Functor.map_comp, Functor.map_comp,
      latentSpaceForgetfulCompHausFunctor_forget,
      operatorObservationCompHausReadoutHom_forget]
    change latentSpaceForgetfulFunctor.map f ≫ _ =
      _ ≫ compHausToTop.map (operatorObservationRangeCompHausHomOfMorphism f)
    rw [operatorObservationRangeCompHausHomOfMorphism_forget]
    apply TopCat.hom_ext
    ext x
    simp only [TopCat.comp_app, TopCat.ofHom]
    apply Subtype.ext
    change S.operatorObservationMap (f.latentMap x) =
      operatorObservationActionOfMorphism f (S.operatorObservationMap x)
    exact funext (fun i => f.observation_natural x i)

theorem operatorObservationCompHausReadoutNatTrans_naturality_apply
    {F G : NoncommutativeObservableTopologicalCovariantFlow S}
    (f : F ⟶ G) (x : X) :
    ((latentSpaceForgetfulCompHausFunctor (S := S)).map f ≫
        (operatorObservationCompHausReadoutNatTrans (S := S)).app G) x =
      ((operatorObservationCompHausReadoutNatTrans (S := S)).app F ≫
        (operatorObservationRangeCompHausFunctor (S := S)).map f) x := by
  exact congrArg (fun h => h x)
    ((operatorObservationCompHausReadoutNatTrans (S := S)).naturality f)

end InfoGeometry.Topology
