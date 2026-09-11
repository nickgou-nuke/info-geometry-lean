import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentCore

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Native `TopCat` readout for finite continuous observables

The algebraic/topological core already provides a joint observation map and
its observational quotient.  This file exposes that existing construction as
`TopCat` morphisms.  It introduces no new quotient, topology, or analytic
claim.
-/

def finiteContinuousObservableObservationTopCatHom
    {X ι : Type} [TopologicalSpace X]
    [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    TopCat.of X ⟶ TopCat.of (ι → ℝ) :=
  TopCat.ofHom
    { toFun := S.observationMap
      continuous_toFun := continuous_observationMap S }

def finiteContinuousObservableQuotientTopCatHom
    {X ι : Type} [TopologicalSpace X]
    [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    TopCat.of X ⟶ TopCat.of (ObservationalQuotient S) :=
  TopCat.ofHom
    { toFun := observationalQuotientMap S
      continuous_toFun := continuous_observationalQuotientMap S }

def finiteContinuousObservableReadoutTopCatHom
    {X ι : Type} [TopologicalSpace X]
    [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    TopCat.of (ObservationalQuotient S) ⟶ TopCat.of (ι → ℝ) :=
  TopCat.ofHom
    { toFun := observationalQuotientReadout S
      continuous_toFun := continuous_observationalQuotientReadout S }

theorem finiteContinuousObservableTopCat_observation_triangle
    {X ι : Type} [TopologicalSpace X]
    [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    finiteContinuousObservableQuotientTopCatHom S ≫
        finiteContinuousObservableReadoutTopCatHom S =
      finiteContinuousObservableObservationTopCatHom S := by
  apply TopCat.hom_ext
  ext x
  simp [finiteContinuousObservableQuotientTopCatHom, finiteContinuousObservableReadoutTopCatHom,
    finiteContinuousObservableObservationTopCatHom, TopCat.ofHom, observationalQuotientReadout_mk]

theorem finiteContinuousObservableQuotientTopCatHom_isQuotientMap
    {X ι : Type} [TopologicalSpace X]
    [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    Topology.IsQuotientMap
      (finiteContinuousObservableQuotientTopCatHom S) := by
  change Topology.IsQuotientMap (observationalQuotientMap S)
  exact isQuotientMap_observationalQuotientMap S

theorem finiteContinuousObservableReadoutTopCatHom_injective
    {X ι : Type} [TopologicalSpace X]
    [Fintype ι]
    (S : FiniteContinuousObservableSystem X ι) :
    Function.Injective (finiteContinuousObservableReadoutTopCatHom S) := by
  change Function.Injective (observationalQuotientReadout S)
  exact observationalQuotientReadout_injective S

end InfoGeometry.Topology
