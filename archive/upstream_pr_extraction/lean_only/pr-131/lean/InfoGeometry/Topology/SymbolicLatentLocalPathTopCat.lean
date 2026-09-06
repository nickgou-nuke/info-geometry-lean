import Mathlib
import InfoGeometry.Topology.SymbolicLatentLocalPath
import InfoGeometry.Topology.SymbolicLatentPathImageTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` factorization for a chart-local symbolic path

The local-path owner proves that the path image lies in one chart domain.
This file exposes that restriction categorically while retaining the ambient
path-image inclusion.
-/

abbrev SymbolicLatentLocalPathImage
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :=
  {y // y ∈ γ.image}

def SymbolicLatentLocalPath.imageEvaluationTopCatHom
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    TopCat.of SymbolicPathDomain ⟶
      TopCat.of (SymbolicLatentLocalPathImage γ) :=
  TopCat.ofHom
    { toFun := fun t => ⟨γ.path t, ⟨t, rfl⟩⟩
      continuous_toFun := γ.path.continuous.subtype_mk (fun t => ⟨t, rfl⟩) }

def SymbolicLatentLocalPath.imageToChartTopCatHom
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    TopCat.of (SymbolicLatentLocalPathImage γ) ⟶
      TopCat.of (C.domain γ.chart) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨y.1, γ.image_subset_chart y.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk
        (fun y => γ.image_subset_chart y.2) }

def SymbolicLatentLocalPath.imageInclusionTopCatHom
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    TopCat.of (SymbolicLatentLocalPathImage γ) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def SymbolicLatentLocalPath.chartInclusionTopCatHom
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    TopCat.of (C.domain γ.chart) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

theorem SymbolicLatentLocalPath.chartInclusion_isOpenEmbedding
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    Topology.IsOpenEmbedding
      (Subtype.val : C.domain γ.chart → X) := by
  exact (C.isOpen_domain γ.chart).isOpenEmbedding_subtypeVal

theorem SymbolicLatentLocalPath.image_isCompact_topCat
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    IsCompact (γ.image) :=
  γ.image_isCompact

abbrev SymbolicLatentLocalPathPullbackDomain
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :=
  {t // t ∈ γ.pullbackDomain}

def SymbolicLatentLocalPath.pullbackDomainToIntervalTopCatHom
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    TopCat.of (SymbolicLatentLocalPathPullbackDomain γ) ⟶
      TopCat.of SymbolicPathDomain :=
  TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }

def SymbolicLatentLocalPath.intervalToPullbackDomainTopCatHom
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    TopCat.of SymbolicPathDomain ⟶
      TopCat.of (SymbolicLatentLocalPathPullbackDomain γ) :=
  TopCat.ofHom
    { toFun := fun t => ⟨t, by
        rw [γ.pullbackDomain_eq_univ]
        trivial⟩
      continuous_toFun := continuous_id.subtype_mk (fun t => by
        rw [γ.pullbackDomain_eq_univ]
        trivial) }

theorem SymbolicLatentLocalPath.pullbackDomainToIntervalTopCatHom_isIso
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    IsIso (γ.pullbackDomainToIntervalTopCatHom) := by
  refine IsIso.mk ⟨γ.intervalToPullbackDomainTopCatHom, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext t
    rfl
  · apply TopCat.hom_ext
    ext t
    rfl

theorem SymbolicLatentLocalPath.image_chart_factorization
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    γ.imageToChartTopCatHom ≫ γ.chartInclusionTopCatHom =
      γ.imageInclusionTopCatHom := by
  ext y
  rfl

theorem SymbolicLatentLocalPath.image_evaluation_factorization
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    γ.imageEvaluationTopCatHom ≫ γ.imageInclusionTopCatHom =
      symbolicLatentPathImageAmbientEvaluationTopCatHom γ.path := by
  ext t
  rfl

theorem SymbolicLatentLocalPath.imageEvaluation_chart_factorization
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C) :
    γ.imageEvaluationTopCatHom ≫ γ.imageToChartTopCatHom =
      TopCat.ofHom
        { toFun := fun t => ⟨γ.path t, γ.stays_in_chart t⟩
          continuous_toFun := γ.path.continuous.subtype_mk
            (fun t => γ.stays_in_chart t) } := by
  ext t
  rfl

theorem SymbolicLatentLocalPath.image_chart_factorization_unique
    {X κ : Type} [TopologicalSpace X] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    (γ : SymbolicLatentLocalPath X κ C)
    {u : TopCat.of (SymbolicLatentLocalPathImage γ) ⟶
      TopCat.of (C.domain γ.chart)}
    (hu : u ≫ γ.chartInclusionTopCatHom =
      γ.imageInclusionTopCatHom) :
    u = γ.imageToChartTopCatHom := by
  apply TopCat.hom_ext
  ext y
  have hy := congrArg (fun m => m y) hu
  simpa [SymbolicLatentLocalPath.imageToChartTopCatHom,
    SymbolicLatentLocalPath.chartInclusionTopCatHom,
    SymbolicLatentLocalPath.imageInclusionTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hy

end InfoGeometry.Topology
