import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartEquivalenceHomotopyQuotient
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` readout of reversible chart transport

The chart-equivalence owner supplies an actual map on path-homotopy
quotients.  This file exposes that map categorically and records the
endpoint-evaluation square inherited from generic homotopy functoriality.
-/

def SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D) :
    TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) ⟶
      TopCat.of (SymbolicLatentPathHomotopyQuotient (X := Y)) :=
  symbolicLatentPathHomotopyQuotientTopCatHom
    F.toMorphism.continuousMap

theorem SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom_apply
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    F.pathHomotopyQuotientTopCatHom q =
      F.pathHomotopyQuotientEquiv q := by
  rfl

theorem SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom_endpoint_natural
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D) :
    F.pathHomotopyQuotientTopCatHom ≫
        symbolicLatentPathHomotopyEndpointTopCatHom =
      symbolicLatentPathHomotopyEndpointTopCatHom ≫
        symbolicLatentPathHomotopyEndpointMapTopCatHom
          F.toMorphism.continuousMap := by
  exact symbolicLatentPathHomotopyEndpointTopCatHom_natural
    F.toMorphism.continuousMap

theorem SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom_id
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι} :
    (SymbolicLatentChartEquivalence.id C).pathHomotopyQuotientTopCatHom =
      𝟙 (TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X))) := by
  ext q
  change mapSymbolicLatentPathHomotopyQuotient
      (SymbolicLatentChartEquivalence.id C).toMorphism.continuousMap q = q
  simpa [SymbolicLatentChartEquivalence.id,
    SymbolicLatentChartEquivalence.toMorphism,
    SymbolicLatentChartMorphism.id] using
    congrFun (mapSymbolicLatentPathHomotopyQuotient_id (X := X)) q

theorem SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom_comp
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D) :
    (G.comp F).pathHomotopyQuotientTopCatHom =
      F.pathHomotopyQuotientTopCatHom ≫
        G.pathHomotopyQuotientTopCatHom := by
  ext q
  change mapSymbolicLatentPathHomotopyQuotient
      (G.comp F).toMorphism.continuousMap q =
    mapSymbolicLatentPathHomotopyQuotient G.toMorphism.continuousMap
      (mapSymbolicLatentPathHomotopyQuotient F.toMorphism.continuousMap q)
  simpa [SymbolicLatentChartEquivalence.comp,
    SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom] using
    congrFun
      (SymbolicLatentChartMorphism.mapPathHomotopyQuotient_comp
        (G := G.toMorphism) (F := F.toMorphism)) q

theorem SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom_comp_apply
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    {E : SymbolicLatentChart Z ι}
    (G : SymbolicLatentChartEquivalence D E)
    (F : SymbolicLatentChartEquivalence C D)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    (G.comp F).pathHomotopyQuotientTopCatHom q =
      (F.pathHomotopyQuotientTopCatHom ≫
        G.pathHomotopyQuotientTopCatHom) q := by
  simpa using
    congrArg (fun m => m q)
      (SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom_comp
        (G := G) (F := F))

def SymbolicLatentChartEquivalence.pathHomotopyQuotientInverseTopCatHom
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D) :
    TopCat.of (SymbolicLatentPathHomotopyQuotient (X := Y)) ⟶
      TopCat.of (SymbolicLatentPathHomotopyQuotient (X := X)) :=
  F.symm.pathHomotopyQuotientTopCatHom

theorem SymbolicLatentChartEquivalence.pathHomotopyQuotientTopCatHom_isIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D) :
    IsIso F.pathHomotopyQuotientTopCatHom := by
  refine IsIso.mk ⟨F.pathHomotopyQuotientInverseTopCatHom, ?_, ?_⟩
  · change F.pathHomotopyQuotientTopCatHom ≫
      F.symm.pathHomotopyQuotientTopCatHom = _
    rw [← F.symm.pathHomotopyQuotientTopCatHom_comp F]
    ext q
    have hlatent :
        (F.symm.comp F).toMorphism.continuousMap = ContinuousMap.id X := by
      ext u
      simp [SymbolicLatentChartEquivalence.symm,
        SymbolicLatentChartEquivalence.comp]
      rfl
    change mapSymbolicLatentPathHomotopyQuotient
        (F.symm.comp F).toMorphism.continuousMap q = q
    rw [hlatent]
    exact congrFun (mapSymbolicLatentPathHomotopyQuotient_id (X := X)) q
  · change F.symm.pathHomotopyQuotientTopCatHom ≫
      F.pathHomotopyQuotientTopCatHom = _
    rw [← F.pathHomotopyQuotientTopCatHom_comp F.symm]
    ext q
    have hlatent :
        (F.comp F.symm).toMorphism.continuousMap = ContinuousMap.id Y := by
      ext u
      simp [SymbolicLatentChartEquivalence.symm,
        SymbolicLatentChartEquivalence.comp]
      rfl
    change mapSymbolicLatentPathHomotopyQuotient
        (F.comp F.symm).toMorphism.continuousMap q = q
    rw [hlatent]
    exact congrFun (mapSymbolicLatentPathHomotopyQuotient_id (X := Y)) q

end InfoGeometry.Topology
