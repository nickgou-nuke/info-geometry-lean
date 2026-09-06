import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathFamily
import InfoGeometry.Topology.SymbolicLatentObservedFamilyTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Generic `TopCat` readout for a symbolic-latent path family

The observed-family owner provides the same parameter inclusions for the
common corridor.  This file exposes the underlying latent family itself and
its two endpoint evaluations as `TopCat` morphisms.
-/

def symbolicLatentPathFamilyTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (P × SymbolicPathDomain) ⟶ TopCat.of X :=
  TopCat.ofHom H

def symbolicLatentPathFamilyStartTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of P ⟶ TopCat.of X :=
  TopCat.ofHom H.startFamily

def symbolicLatentPathFamilyFinishTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of P ⟶ TopCat.of X :=
  TopCat.ofHom H.finishFamily

def symbolicLatentPathFamilyEndpointsTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of P ⟶ TopCat.of (X × X) :=
  TopCat.ofHom
    { toFun := fun p => (H.startFamily p, H.finishFamily p)
      continuous_toFun := H.startFamily.continuous.prodMk H.finishFamily.continuous }

theorem symbolicLatentPathFamilyTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (q : P × SymbolicPathDomain) :
    symbolicLatentPathFamilyTopCatHom H q = H q :=
  rfl

theorem symbolicLatentPathFamilyStartTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (p : P) :
    symbolicLatentPathFamilyStartTopCatHom H p = H.startFamily p :=
  rfl

theorem symbolicLatentPathFamilyFinishTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (p : P) :
    symbolicLatentPathFamilyFinishTopCatHom H p = H.finishFamily p :=
  rfl

theorem symbolicLatentPathFamilyEndpointsTopCatHom_apply
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) (p : P) :
    symbolicLatentPathFamilyEndpointsTopCatHom H p =
      (H.startFamily p, H.finishFamily p) :=
  rfl

def symbolicLatentPathFamilyEndpointsLeftProjectionTopCatHom
    {X : Type} [TopologicalSpace X] :
    TopCat.of (X × X) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Prod.fst
      continuous_toFun := continuous_fst }

def symbolicLatentPathFamilyEndpointsRightProjectionTopCatHom
    {X : Type} [TopologicalSpace X] :
    TopCat.of (X × X) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Prod.snd
      continuous_toFun := continuous_snd }

theorem symbolicLatentPathFamilyEndpointsTopCatHom_left
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyEndpointsTopCatHom H ≫
        symbolicLatentPathFamilyEndpointsLeftProjectionTopCatHom (X := X) =
      symbolicLatentPathFamilyStartTopCatHom H := by
  ext p
  rfl

theorem symbolicLatentPathFamilyEndpointsTopCatHom_right
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyEndpointsTopCatHom H ≫
        symbolicLatentPathFamilyEndpointsRightProjectionTopCatHom (X := X) =
      symbolicLatentPathFamilyFinishTopCatHom H := by
  ext p
  rfl

theorem symbolicLatentPathFamily_start_natural
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyStartParameterTopCatHom P ≫
        symbolicLatentPathFamilyTopCatHom H =
      symbolicLatentPathFamilyStartTopCatHom H := by
  ext p
  rfl

theorem symbolicLatentPathFamily_finish_natural
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyFinishParameterTopCatHom P ≫
        symbolicLatentPathFamilyTopCatHom H =
      symbolicLatentPathFamilyFinishTopCatHom H := by
  ext p
  rfl

end InfoGeometry.Topology
