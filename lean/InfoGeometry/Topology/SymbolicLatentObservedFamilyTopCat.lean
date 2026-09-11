import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservedFamily
import InfoGeometry.Topology.SymbolicLatentChartHomotopyBridge

namespace InfoGeometry.Topology

open CategoryTheory
open scoped CategoryTheory

/-!
# `TopCat` readout of jointly continuous observed path families

The family owner already supplies compact-open/continuous data.  This file
exposes the joint observed family and its endpoint evaluations as native
categorical morphisms.
-/

def observedSymbolicLatentPathFamilyTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    TopCat.of (P × SymbolicPathDomain) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom (observedSymbolicLatentPathFamily S H h_obs)

theorem observedSymbolicLatentPathFamilyTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) (q : P × SymbolicPathDomain) :
    observedSymbolicLatentPathFamilyTopCatHom S H h_obs q =
      symbolicObservationMap S (H q) :=
  rfl

def observedSymbolicLatentPathFamilyStart
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) : C(P, SymbolicFeatureSpace ι) :=
  (symbolicObservationContinuousMap S).comp H.startFamily

def observedSymbolicLatentPathFamilyFinish
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) : C(P, SymbolicFeatureSpace ι) :=
  (symbolicObservationContinuousMap S).comp H.finishFamily

theorem observedSymbolicLatentPathFamilyStart_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) (p : P) :
    observedSymbolicLatentPathFamilyStart S H h_obs p =
      symbolicObservationMap S (H (p, 0)) :=
  rfl

theorem observedSymbolicLatentPathFamilyFinish_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) (p : P) :
    observedSymbolicLatentPathFamilyFinish S H h_obs p =
      symbolicObservationMap S (H (p, 1)) :=
  rfl

def observedSymbolicLatentPathFamilyStartTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    TopCat.of P ⟶ TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom (observedSymbolicLatentPathFamilyStart S H h_obs)

def observedSymbolicLatentPathFamilyFinishTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    TopCat.of P ⟶ TopCat.of (SymbolicFeatureSpace ι) :=
  TopCat.ofHom (observedSymbolicLatentPathFamilyFinish S H h_obs)

def symbolicLatentPathFamilyStartParameterTopCatHom
    (P : Type) [TopologicalSpace P] :
    TopCat.of P ⟶ TopCat.of (P × SymbolicPathDomain) :=
  TopCat.ofHom
    { toFun := fun p => (p, 0)
      continuous_toFun := continuous_id.prodMk continuous_const }

def symbolicLatentPathFamilyFinishParameterTopCatHom
    (P : Type) [TopologicalSpace P] :
    TopCat.of P ⟶ TopCat.of (P × SymbolicPathDomain) :=
  TopCat.ofHom
    { toFun := fun p => (p, 1)
      continuous_toFun := continuous_id.prodMk continuous_const }

theorem observedSymbolicLatentPathFamilyStartTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) (p : P) :
    observedSymbolicLatentPathFamilyStartTopCatHom S H h_obs p =
      observedSymbolicLatentPathFamilyStart S H h_obs p :=
  rfl

theorem observedSymbolicLatentPathFamilyFinishTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) (p : P) :
    observedSymbolicLatentPathFamilyFinishTopCatHom S H h_obs p =
      observedSymbolicLatentPathFamilyFinish S H h_obs p :=
  rfl

theorem observedSymbolicLatentPathFamily_start_natural
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    (symbolicLatentPathFamilyStartParameterTopCatHom P) ≫
        observedSymbolicLatentPathFamilyTopCatHom S H h_obs =
      observedSymbolicLatentPathFamilyStartTopCatHom S H h_obs := by
  ext p
  rfl

theorem observedSymbolicLatentPathFamily_finish_natural
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    (symbolicLatentPathFamilyFinishParameterTopCatHom P) ≫
        observedSymbolicLatentPathFamilyTopCatHom S H h_obs =
      observedSymbolicLatentPathFamilyFinishTopCatHom S H h_obs := by
  ext p
  rfl

end InfoGeometry.Topology
