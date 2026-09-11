import InfoGeometry.Topology.SymbolicLatentPathImageFeasibleCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathImageTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# CompHaus evaluation of an observed symbolic-latent path

The parameter interval is compact Hausdorff and the observed path image is a
compact Hausdorff subtype.  Thus the existing `TopCat` evaluation and
inclusion maps sorry a genuine `CompHaus` source/target packaging.  The
ambient feature space is intentionally kept in `TopCat`, since it need not be
compact.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

noncomputable def symbolicPathDomainCompHaus : CompHaus :=
  CompHaus.of SymbolicPathDomain

noncomputable def observedSymbolicLatentPathImageEvaluationCompHausHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    symbolicPathDomainCompHaus ⟶
      observedSymbolicLatentPathImageCompHaus S γ := by
  letI : CompactSpace (observedSymbolicLatentPathImage S γ) :=
    observedSymbolicLatentPathImage_compactSpace S γ
  dsimp [symbolicPathDomainCompHaus,
    observedSymbolicLatentPathImageCompHaus]
  change CompHaus.of SymbolicPathDomain ⟶
    CompHaus.of (observedSymbolicLatentPathImage S γ)
  exact ⟨observedSymbolicLatentPathImageEvaluationTopCatHom S γ⟩

theorem observedSymbolicLatentPathImageEvaluationCompHausHom_forget
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    compHausToTop.map
        (observedSymbolicLatentPathImageEvaluationCompHausHom S γ) =
      observedSymbolicLatentPathImageEvaluationTopCatHom S γ := by
  apply TopCat.hom_ext
  ext t
  rfl

@[simp] theorem observedSymbolicLatentPathImageEvaluationCompHausHom_apply
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X)
    (t : SymbolicPathDomain) :
    observedSymbolicLatentPathImageEvaluationCompHausHom S γ t =
      ⟨symbolicObservationPath S γ t, ⟨t, rfl⟩⟩ :=
  rfl

noncomputable def observedSymbolicLatentPathImageInclusionCompHausTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    compHausToTop.obj (observedSymbolicLatentPathImageCompHaus S γ) ⟶
      TopCat.of (SymbolicFeatureSpace ι) := by
  change TopCat.of (observedSymbolicLatentPathImage S γ) ⟶
    TopCat.of (SymbolicFeatureSpace ι)
  exact observedSymbolicLatentPathImageInclusionTopCatHom S γ

theorem observedSymbolicLatentPathImageCompHaus_evaluation_factorization
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (γ : SymbolicLatentPath X) :
    compHausToTop.map
        (observedSymbolicLatentPathImageEvaluationCompHausHom S γ) ≫
        observedSymbolicLatentPathImageInclusionCompHausTopCatHom S γ =
      observedSymbolicLatentPathImageAmbientEvaluationTopCatHom S γ := by
  exact observedSymbolicLatentPathImage_evaluation_factorization S γ

end
end InfoGeometry.Topology
