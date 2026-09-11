import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartMorphism

/-!
# Equivalences of symbolic latent charts

An equivalence consists of a homeomorphism of latent carriers and a
homeomorphism of feature spaces satisfying one explicit intertwining law.
The induced region equivalence is proved without introducing a metric or a
probabilistic interpretation.
-/

namespace InfoGeometry.Topology

structure SymbolicLatentChartEquivalence
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι)
    (D : SymbolicLatentChart Y ι) where
  latentEquiv : X ≃ₜ Y
  featureEquiv : SymbolicFeatureSpace ι ≃ₜ SymbolicFeatureSpace ι
  intertwines : ∀ x,
    featureEquiv (symbolicObservationMap C.system x) =
      symbolicObservationMap D.system (latentEquiv x)

namespace SymbolicLatentChartEquivalence

def id
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Fintype ι]
    (C : SymbolicLatentChart X ι) :
    SymbolicLatentChartEquivalence C C where
  latentEquiv := Homeomorph.refl X
  featureEquiv := Homeomorph.refl (SymbolicFeatureSpace ι)
  intertwines := by intro x; rfl

def comp
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D) :
    SymbolicLatentChartEquivalence C E where
  latentEquiv := F.latentEquiv.trans G.latentEquiv
  featureEquiv := F.featureEquiv.trans G.featureEquiv
  intertwines := by
    intro x
    change G.featureEquiv
        (F.featureEquiv (symbolicObservationMap C.system x)) =
      symbolicObservationMap E.system
        (G.latentEquiv (F.latentEquiv x))
    rw [F.intertwines, G.intertwines]

def symm
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D) :
    SymbolicLatentChartEquivalence D C where
  latentEquiv := F.latentEquiv.symm
  featureEquiv := F.featureEquiv.symm
  intertwines := by
    intro y
    apply F.featureEquiv.injective
    simpa using (F.intertwines (F.latentEquiv.symm y)).symm

@[simp] theorem comp_latentEquiv
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D) :
    (G.comp F).latentEquiv = F.latentEquiv.trans G.latentEquiv :=
  rfl

@[simp] theorem comp_featureEquiv
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D) :
    (G.comp F).featureEquiv = F.featureEquiv.trans G.featureEquiv :=
  rfl

end SymbolicLatentChartEquivalence

def SymbolicLatentChartEquivalence.toMorphism
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D) :
    SymbolicLatentChartMorphism C D where
  toFun := F.latentEquiv
  continuous_toFun := F.latentEquiv.continuous_toFun
  featureMap := F.featureEquiv
  continuous_featureMap := F.featureEquiv.continuous_toFun
  intertwines := F.intertwines

def latentFeatureRegionHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι)) :
    {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)} ≃ₜ
      {y // y ∈ latentFeatureRegion D R} :=
  { toEquiv :=
      { toFun := fun x =>
          ⟨F.latentEquiv x, by
            change symbolicObservationMap D.system (F.latentEquiv x) ∈ R
            rw [← F.intertwines x]
            exact x.property⟩
        invFun := fun y =>
          ⟨F.latentEquiv.symm y, by
            change F.featureEquiv (symbolicObservationMap C.system
              (F.latentEquiv.symm y)) ∈ R
            have h := F.intertwines (F.latentEquiv.symm y)
            rw [h]
            simp
            exact y.property⟩
        left_inv := by
          intro x
          apply Subtype.ext
          simp
        right_inv := by
          intro y
          apply Subtype.ext
          simp }
    continuous_toFun := by
      exact (F.latentEquiv.continuous_toFun.comp continuous_subtype_val).subtype_mk
        (fun x => by
          change symbolicObservationMap D.system (F.latentEquiv x) ∈ R
          rw [← F.intertwines x]
          exact x.property)
    continuous_invFun := by
      exact (F.latentEquiv.symm.continuous_toFun.comp continuous_subtype_val).subtype_mk
        (fun y => by
          change F.featureEquiv (symbolicObservationMap C.system
            (F.latentEquiv.symm y)) ∈ R
          have h := F.intertwines (F.latentEquiv.symm y)
          rw [h]
          simp
          exact y.property) }

@[simp] theorem latentFeatureRegionHomeomorph_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (R : Set (SymbolicFeatureSpace ι))
    (x : {x // x ∈ latentFeatureRegion C (F.featureEquiv ⁻¹' R)}) :
    latentFeatureRegionHomeomorph F R x =
      ⟨F.latentEquiv x, by
        change symbolicObservationMap D.system (F.latentEquiv x) ∈ R
        rw [← F.intertwines x]
        exact x.property⟩ :=
  rfl

end InfoGeometry.Topology
