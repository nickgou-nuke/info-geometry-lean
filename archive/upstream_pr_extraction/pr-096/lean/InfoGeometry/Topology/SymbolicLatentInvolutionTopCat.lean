import Mathlib
import InfoGeometry.Topology.SymbolicLatentInvolutionFixedPoints

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` readout of symbolic-latent involution fixed points

The fixed-point set is already a native closed subset.  This file adds only
the categorical maps forced by the existing continuous involution; it does
not identify the fixed set with an abstract categorical equalizer.
-/

def SymbolicLatentInvolution.toTopCatHom
    {X : Type} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :
    TopCat.of X ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := J
      continuous_toFun := J.continuous }

theorem SymbolicLatentInvolution.toTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) (x : X) :
    J.toTopCatHom x = J x :=
  rfl

theorem SymbolicLatentInvolution.toTopCatHom_square
    {X : Type} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :
    J.toTopCatHom ≫ J.toTopCatHom = 𝟙 (TopCat.of X) := by
  ext x
  exact J.involutive x

theorem SymbolicLatentInvolution.toTopCatHom_isIso
    {X : Type} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :
    IsIso J.toTopCatHom := by
  refine IsIso.mk ⟨J.toTopCatHom, ?_, ?_⟩
  · exact J.toTopCatHom_square
  · exact J.toTopCatHom_square

abbrev SymbolicLatentInvolutionFixedPointObject
    {X : Type} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :=
  TopCat.of (symbolicLatentInvolutionFixedPointSet J)

def SymbolicLatentInvolution.fixedPointInclusion
    {X : Type*} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :
    TopCat.of (symbolicLatentInvolutionFixedPointSet J) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := fun x => x.1
      continuous_toFun := continuous_subtype_val }

theorem SymbolicLatentInvolution.fixedPointInclusion_apply
    {X : Type} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X)
    (x : symbolicLatentInvolutionFixedPointSet J) :
    J.fixedPointInclusion x = x.1 :=
  rfl

theorem SymbolicLatentInvolution.fixedPointInclusion_invariant
    {X : Type} [TopologicalSpace X]
    (J : SymbolicLatentInvolution X) :
    J.fixedPointInclusion ≫ J.toTopCatHom =
      J.fixedPointInclusion := by
  ext x
  exact x.2

end InfoGeometry.Topology
