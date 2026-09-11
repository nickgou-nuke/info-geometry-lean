import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealCl55NativeChiralHodgeIndexBridge

/-!
# Native equivariant chiral complex datum

This owner packages the already constructed native chiral sectors, typed
Hodge--Dirac arrows, restricted actions, and their commuting squares.  It is
an algebraic precursor to an equivariant index construction; it is not a
cohomology theorem, a KKO class, or a claim about a particular Lie group.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeEquivariantChiralComplexBridge

open InfoGeometry.Canonical.RealCl55NativeChiralSectorBridge
open InfoGeometry.Canonical.RealCl55NativeChiralHodgeIndexBridge
open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge

structure NativeEquivariantChiralComplexDatum (G : Type*) [Group G] where
  plusAction : G →* (nativePlusSector →ₗ[ℝ] nativePlusSector)
  minusAction : G →* (nativeMinusSector →ₗ[ℝ] nativeMinusSector)
  plusDirac : nativePlusSector →ₗ[ℝ] nativeMinusSector
  minusDirac : nativeMinusSector →ₗ[ℝ] nativePlusSector
  plus_intertwines : ∀ g,
    (minusAction g).comp plusDirac = plusDirac.comp (plusAction g)
  minus_intertwines : ∀ g,
    (plusAction g).comp minusDirac = minusDirac.comp (minusAction g)
  plus_laplacian : ∀ x : nativePlusSector,
    minusDirac (plusDirac x) = (3 : ℝ) • x
  minus_laplacian : ∀ x : nativeMinusSector,
    plusDirac (minusDirac x) = (3 : ℝ) • x

noncomputable def canonicalNativeEquivariantChiralComplexDatum
    {G : Type*} [Group G] (act : G2IntegratedAction G) :
    NativeEquivariantChiralComplexDatum G where
  plusAction := nativePlusSectorActionHom act
  minusAction := nativeMinusSectorActionHom act
  plusDirac := nativeChiralDiracPlusArrow
  minusDirac := nativeChiralDiracMinusArrow
  plus_intertwines := nativePlusSectorAction_intertwines_chiralDiracPlus act
  minus_intertwines := nativeMinusSectorAction_intertwines_chiralDiracMinus act
  plus_laplacian := nativeChiralDiracMinusArrow_comp_plusArrow_apply
  minus_laplacian := nativeChiralDiracPlusArrow_comp_minusArrow_apply

theorem canonicalNativeEquivariantChiralComplex_plus_intertwines
    {G : Type*} [Group G] (act : G2IntegratedAction G) (g : G) :
    (nativeMinusSectorActionHom act g).comp nativeChiralDiracPlusArrow =
      nativeChiralDiracPlusArrow.comp (nativePlusSectorActionHom act g) := by
  exact nativePlusSectorAction_intertwines_chiralDiracPlus act g

theorem canonicalNativeEquivariantChiralComplex_minus_intertwines
    {G : Type*} [Group G] (act : G2IntegratedAction G) (g : G) :
    (nativePlusSectorActionHom act g).comp nativeChiralDiracMinusArrow =
      nativeChiralDiracMinusArrow.comp (nativeMinusSectorActionHom act g) := by
  exact nativeMinusSectorAction_intertwines_chiralDiracMinus act g

end InfoGeometry.Canonical.RealCl55NativeEquivariantChiralComplexBridge
