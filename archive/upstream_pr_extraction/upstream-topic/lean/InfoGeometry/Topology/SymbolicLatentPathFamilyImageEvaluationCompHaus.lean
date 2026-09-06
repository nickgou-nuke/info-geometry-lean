import InfoGeometry.Topology.SymbolicLatentPathFamilyImageEquivCompHaus
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# CompHaus evaluation of symbolic-latent path-family images

For a compact Hausdorff parameter carrier and a Hausdorff latent carrier, the
product parameter space and the image of a jointly continuous path family are
compact Hausdorff.  The evaluation map is therefore a genuine `CompHaus`
morphism, while the ambient inclusion remains a `TopCat` morphism because the
ambient latent carrier need not be compact.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable def symbolicLatentPathFamilyDomainCompHaus
    {P : Type} [TopologicalSpace P] [CompactSpace P] [T2Space P] : CompHaus :=
  CompHaus.of (P × SymbolicPathDomain)

noncomputable def symbolicLatentPathFamilyImageEvaluationCompHausHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [T2Space P]
    [T2Space X]
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyDomainCompHaus (P := P) ⟶
      symbolicLatentPathFamilyImageCompHaus H := by
  letI : CompactSpace (symbolicLatentPathFamilyImage H) :=
    isCompact_iff_compactSpace.mp
      (isCompact_symbolicLatentPathFamilyImage H)
  dsimp [symbolicLatentPathFamilyDomainCompHaus,
    symbolicLatentPathFamilyImageCompHaus]
  change CompHaus.of (P × SymbolicPathDomain) ⟶
    CompHaus.of (symbolicLatentPathFamilyImage H)
  exact ⟨symbolicLatentPathFamilyImageEvaluationTopCatHom H⟩

theorem symbolicLatentPathFamilyImageEvaluationCompHausHom_forget
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [T2Space P]
    [T2Space X]
    (H : SymbolicLatentPathFamily P X) :
    compHausToTop.map
        (symbolicLatentPathFamilyImageEvaluationCompHausHom H) =
      symbolicLatentPathFamilyImageEvaluationTopCatHom H := by
  apply TopCat.hom_ext
  ext q
  rfl

@[simp] theorem symbolicLatentPathFamilyImageEvaluationCompHausHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [T2Space P]
    [T2Space X]
    (H : SymbolicLatentPathFamily P X)
    (q : P × SymbolicPathDomain) :
    symbolicLatentPathFamilyImageEvaluationCompHausHom H q =
      ⟨H q, ⟨q, rfl⟩⟩ :=
  rfl

noncomputable def symbolicLatentPathFamilyImageInclusionCompHausTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [T2Space P]
    [T2Space X]
    (H : SymbolicLatentPathFamily P X) :
    compHausToTop.obj (symbolicLatentPathFamilyImageCompHaus H) ⟶
      TopCat.of X := by
  change TopCat.of (symbolicLatentPathFamilyImage H) ⟶ TopCat.of X
  exact symbolicLatentPathFamilyImageInclusionTopCatHom H

theorem symbolicLatentPathFamilyImageCompHaus_evaluation_factorization
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [T2Space P]
    [T2Space X]
    (H : SymbolicLatentPathFamily P X) :
    compHausToTop.map
        (symbolicLatentPathFamilyImageEvaluationCompHausHom H) ≫
        symbolicLatentPathFamilyImageInclusionCompHausTopCatHom H =
      TopCat.ofHom H := by
  exact symbolicLatentPathFamilyImage_evaluation_factorization H

theorem SymbolicLatentChartEquivalence.imageCompHausEvaluation_natural
    {P X Y : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace P] [T2Space P]
    [T2Space X] [T2Space Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageEvaluationCompHausHom H ≫
        (F.imageHomeomorphCompHausIso H).hom =
      symbolicLatentPathFamilyImageEvaluationCompHausHom (F.mapFamily H) := by
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  apply hFF.map_injective
  rw [Functor.map_comp]
  rw [symbolicLatentPathFamilyImageEvaluationCompHausHom_forget,
    F.imageHomeomorphCompHausIso_hom_forget,
    symbolicLatentPathFamilyImageEvaluationCompHausHom_forget]
  apply TopCat.hom_ext
  ext q
  rfl

theorem SymbolicLatentChartEquivalence.imageCompHausEvaluation_natural_comp
    {P X Y Z : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace P] [T2Space P]
    [T2Space X] [T2Space Y] [T2Space Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageEvaluationCompHausHom H ≫
        (F.imageHomeomorphCompHausIso H).hom ≫
        (G.imageHomeomorphCompHausIso (F.mapFamily H)).hom =
      symbolicLatentPathFamilyImageEvaluationCompHausHom
        ((G.comp F).mapFamily H) := by
  rw [← Category.assoc,
    F.imageCompHausEvaluation_natural H,
    G.imageCompHausEvaluation_natural (F.mapFamily H)]
  have hmap : G.mapFamily (F.mapFamily H) = (G.comp F).mapFamily H := by
    ext q
    rfl
  cases hmap
  ext q
  rfl

end InfoGeometry.Topology
