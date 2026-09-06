import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientChartBridge
import InfoGeometry.Topology.SymbolicLatentChartEquivalence

namespace InfoGeometry.Topology

/-!
# Reversible chart transport on symbolic-latent homotopy quotients

A chart equivalence transports homotopy classes by an actual `Equiv`.  The
inverse is built from the existing latent homeomorphism inverse; no new
topological carrier is introduced.
-/

def SymbolicLatentChartEquivalence.inverseMorphism
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D) :
    SymbolicLatentChartMorphism D C where
  toFun := F.latentEquiv.symm
  continuous_toFun := F.latentEquiv.symm.continuous_toFun
  featureMap := F.featureEquiv.symm
  continuous_featureMap := F.featureEquiv.symm.continuous_toFun
  intertwines := by
    intro y
    have h := F.intertwines (F.latentEquiv.symm y)
    have h' := congrArg F.featureEquiv.symm h
    simpa using h'.symm

def SymbolicLatentChartEquivalence.pathHomotopyQuotientEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D) :
    SymbolicLatentPathHomotopyQuotient (X := X) ≃
      SymbolicLatentPathHomotopyQuotient (X := Y) where
  toFun := F.toMorphism.mapPathHomotopyQuotient
  invFun := F.inverseMorphism.mapPathHomotopyQuotient
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro γ
    change (mapSymbolicLatentPathHomotopyQuotient
        F.inverseMorphism.continuousMap ∘
      mapSymbolicLatentPathHomotopyQuotient
        F.toMorphism.continuousMap)
      (symbolicLatentPathHomotopyQuotientMap γ) =
      symbolicLatentPathHomotopyQuotientMap γ
    rw [← mapSymbolicLatentPathHomotopyQuotient_comp
      (f := F.toMorphism.continuousMap)
      (g := F.inverseMorphism.continuousMap)]
    have hcomp :
        F.inverseMorphism.continuousMap.comp F.toMorphism.continuousMap =
          ContinuousMap.id X := by
      ext x
      exact F.latentEquiv.left_inv x
    rw [hcomp, mapSymbolicLatentPathHomotopyQuotient_id]
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro γ
    change (mapSymbolicLatentPathHomotopyQuotient
        F.toMorphism.continuousMap ∘
      mapSymbolicLatentPathHomotopyQuotient
        F.inverseMorphism.continuousMap)
      (symbolicLatentPathHomotopyQuotientMap γ) =
      symbolicLatentPathHomotopyQuotientMap γ
    rw [← mapSymbolicLatentPathHomotopyQuotient_comp
      (f := F.inverseMorphism.continuousMap)
      (g := F.toMorphism.continuousMap)]
    have hcomp :
        F.toMorphism.continuousMap.comp F.inverseMorphism.continuousMap =
          ContinuousMap.id Y := by
      ext y
      exact F.latentEquiv.right_inv y
    rw [hcomp, mapSymbolicLatentPathHomotopyQuotient_id]
    rfl

theorem SymbolicLatentChartEquivalence.pathHomotopyQuotientEquiv_endpoint
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartEquivalence C D)
    (q : SymbolicLatentPathHomotopyQuotient (X := X)) :
    symbolicLatentPathHomotopyEndpointMap
        (F.pathHomotopyQuotientEquiv q) =
      (fun p => (F.latentEquiv p.1, F.latentEquiv p.2))
        (symbolicLatentPathHomotopyEndpointMap q) := by
  exact F.toMorphism.mapPathHomotopyQuotient_endpoint q

end InfoGeometry.Topology
