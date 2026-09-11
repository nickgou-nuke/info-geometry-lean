import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageTopCat
import InfoGeometry.Topology.SymbolicLatentPathReparametrization
import InfoGeometry.Topology.SymbolicLatentPathReparametrizationComposition

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Reparametrization of jointly continuous symbolic-latent path families

An endpoint-fixing path reparametrization lifts by precomposition in the path
coordinate.  The lift is kept separate from homotopy quotients: at this layer
we only use continuity, endpoint preservation, and the induced map between
the two family-image subtypes.
-/

def reparametrizeSymbolicLatentPathFamily
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    SymbolicLatentPathFamily P X :=
  { toFun := fun q => H (q.1, R.parameter q.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk
        (R.parameter.continuous.comp continuous_snd)) }

theorem reparametrizeSymbolicLatentPathFamily_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (q : P × SymbolicPathDomain) :
    reparametrizeSymbolicLatentPathFamily R H q =
      H (q.1, R.parameter q.2) :=
  rfl

theorem reparametrizeSymbolicLatentPathFamily_comp
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R S : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    reparametrizeSymbolicLatentPathFamily R
        (reparametrizeSymbolicLatentPathFamily S H) =
      reparametrizeSymbolicLatentPathFamily
        (composeSymbolicLatentPathReparametrization R S) H := by
  ext q
  rfl

def identitySymbolicLatentPathReparametrization :
    SymbolicLatentPathReparametrization :=
  ⟨ContinuousMap.id SymbolicPathDomain, by simp⟩

theorem reparametrizeSymbolicLatentPathFamily_identity
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    reparametrizeSymbolicLatentPathFamily
        identitySymbolicLatentPathReparametrization H = H := by
  ext q
  rfl

def symbolicLatentPathFamilyParameterReparametrizationTopCatHom
    {P : Type} [TopologicalSpace P]
    (R : SymbolicLatentPathReparametrization) :
    TopCat.of (P × SymbolicPathDomain) ⟶
      TopCat.of (P × SymbolicPathDomain) :=
  TopCat.ofHom
    { toFun := fun q => (q.1, R.parameter q.2)
      continuous_toFun := continuous_fst.prodMk
        (R.parameter.continuous.comp continuous_snd) }

@[simp] theorem symbolicLatentPathFamilyParameterReparametrizationTopCatHom_apply
    {P : Type} [TopologicalSpace P]
    (R : SymbolicLatentPathReparametrization)
    (q : P × SymbolicPathDomain) :
    symbolicLatentPathFamilyParameterReparametrizationTopCatHom R q =
      (q.1, R.parameter q.2) :=
  rfl

theorem symbolicLatentPathFamilyParameterReparametrizationTopCatHom_comp
    {P : Type} [TopologicalSpace P]
    (R S : SymbolicLatentPathReparametrization) :
      symbolicLatentPathFamilyParameterReparametrizationTopCatHom
          (P := P) (composeSymbolicLatentPathReparametrization R S) =
        symbolicLatentPathFamilyParameterReparametrizationTopCatHom
          (P := P) R ≫
        symbolicLatentPathFamilyParameterReparametrizationTopCatHom
          (P := P) S := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  dsimp [symbolicLatentPathFamilyParameterReparametrizationTopCatHom,
    composeSymbolicLatentPathReparametrization]
  rfl

theorem symbolicLatentPathFamilyParameterReparametrizationTopCatHom_identity
    {P : Type} [TopologicalSpace P] :
    symbolicLatentPathFamilyParameterReparametrizationTopCatHom
        (P := P) identitySymbolicLatentPathReparametrization =
      𝟙 (TopCat.of (P × SymbolicPathDomain)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  rfl

theorem reparametrizeSymbolicLatentPathFamily_startFamily
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    (reparametrizeSymbolicLatentPathFamily R H).startFamily =
      H.startFamily := by
  ext p
  change H (p, R.parameter 0) = H (p, 0)
  rw [R.at_zero]

theorem reparametrizeSymbolicLatentPathFamily_finishFamily
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    (reparametrizeSymbolicLatentPathFamily R H).finishFamily =
      H.finishFamily := by
  ext p
  change H (p, R.parameter 1) = H (p, 1)
  rw [R.at_one]

def symbolicLatentPathFamilyReparametrizationImageMap
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImage
        (reparametrizeSymbolicLatentPathFamily R H) →
      symbolicLatentPathFamilyImage H :=
  fun y =>
    ⟨y.1, by
      rcases y.2 with ⟨q, hq⟩
      refine ⟨(q.1, R.parameter q.2), ?_⟩
      simpa [reparametrizeSymbolicLatentPathFamily] using hq⟩

def symbolicLatentPathFamilyReparametrizationImageTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (symbolicLatentPathFamilyImage
        (reparametrizeSymbolicLatentPathFamily R H)) ⟶
      TopCat.of (symbolicLatentPathFamilyImage H) :=
  TopCat.ofHom
    { toFun := symbolicLatentPathFamilyReparametrizationImageMap R H
      continuous_toFun :=
        continuous_subtype_val.subtype_mk
          (fun y => (symbolicLatentPathFamilyReparametrizationImageMap R H y).2) }

@[simp] theorem symbolicLatentPathFamilyReparametrizationImageTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (y : symbolicLatentPathFamilyImage
        (reparametrizeSymbolicLatentPathFamily R H)) :
    symbolicLatentPathFamilyReparametrizationImageTopCatHom R H y =
      symbolicLatentPathFamilyReparametrizationImageMap R H y :=
  by
    change symbolicLatentPathFamilyReparametrizationImageMap R H y =
      symbolicLatentPathFamilyReparametrizationImageMap R H y
    rfl

theorem symbolicLatentPathFamilyReparametrizationImageTopCatHom_comp
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R S : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyReparametrizationImageTopCatHom R
        (reparametrizeSymbolicLatentPathFamily S H) ≫
      symbolicLatentPathFamilyReparametrizationImageTopCatHom S H =
      symbolicLatentPathFamilyReparametrizationImageTopCatHom
        (composeSymbolicLatentPathReparametrization R S) H := by
  have h := reparametrizeSymbolicLatentPathFamily_comp R S H
  cases h
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  rfl

theorem symbolicLatentPathFamilyImageEvaluation_reparametrization_natural
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageEvaluationTopCatHom
        (reparametrizeSymbolicLatentPathFamily R H) ≫
        symbolicLatentPathFamilyReparametrizationImageTopCatHom R H =
      symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
        symbolicLatentPathFamilyImageEvaluationTopCatHom H := by
  ext q
  change H (q.1, R.parameter q.2) = H (q.1, R.parameter q.2)
  rfl

end InfoGeometry.Topology
