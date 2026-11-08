/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationGeometryTransport
import InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms
import InfoGeometry.Algebra.Zorn.SplitOctonionDerivationConjugation

/-!
# Split-octonion automorphisms on native operator differential forms

The existing `conjugateCanonicalDerivation` transports the base Lie algebra.
Mathlib's native conjugation algebra equivalence transports the full
endomorphism algebra. Their compatibility follows from the actual canonical
and vector Zorn coordinate equivalence. The resulting action preserves the
existing canonical Maurer--Cartan form and transports arbitrary curvature.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CanonicalZornAutomorphismDifferentialForms

open InfoGeometry.Canonical
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms

/-- The existing derivation Lie equivalence is native End conjugation. -/
theorem conjugateCanonicalDerivation_val
    (φ : RealSplitOctonionAut) (D : canonicalZornDerivations) :
    (conjugateCanonicalDerivation φ D).1 = φ.1.conjAlgEquiv ℝ D.1 := by
  have hφ (x : InfoGeometry.Canonical.ZornMatrix ℝ) :
      nativeAut φ (canonicalVectorEquiv x) = canonicalVectorEquiv (φ.1 x) := by
    change canonicalVectorEquiv
      (φ.1 (canonicalVectorEquiv.symm (canonicalVectorEquiv x))) = _
    rw [Equiv.symm_apply_apply]
  have hφinv (x : InfoGeometry.Canonical.ZornMatrix ℝ) :
      (nativeAut φ).symm (canonicalVectorEquiv x) =
        canonicalVectorEquiv (φ.1.symm x) := by
    apply (nativeAut φ).injective
    rw [LinearEquiv.apply_symm_apply, hφ, LinearEquiv.apply_symm_apply]
  apply LinearMap.ext
  intro x
  change canonicalVectorEquiv.symm
      (nativeAut φ (canonicalToVectorDerivation D
        ((nativeAut φ).symm (canonicalVectorEquiv x)))) =
    φ.1 (D.1 (φ.1.symm x))
  rw [hφinv, canonicalToVectorDerivation_apply, Equiv.symm_apply_apply,
    hφ, Equiv.symm_apply_apply]

/-- Conjugation intertwines the actual faithful operator derivation action. -/
theorem operatorAction_conjugate
    (φ : RealSplitOctonionAut) (D : canonicalZornDerivations)
    (T : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ)) :
    canonicalZornOperatorDerivationLane.operatorAction
        (conjugateCanonicalDerivation φ D) (φ.1.conjAlgEquiv ℝ T) =
      φ.1.conjAlgEquiv ℝ
        (canonicalZornOperatorDerivationLane.operatorAction D T) := by
  rw [canonicalZornOperatorDerivationLane_operatorAction,
    canonicalZornOperatorDerivationLane_operatorAction,
    conjugateCanonicalDerivation_val, map_sub, map_mul, map_mul]

/-- Simultaneous automorphism action on the existing native one-form carrier. -/
def automorphismOneForm (φ : RealSplitOctonionAut)
    (Γ : OperatorOneForm) : OperatorOneForm :=
  transportOneForm (conjugateCanonicalDerivation φ) (φ.1.conjAlgEquiv ℝ) Γ

@[simp] theorem automorphismOneForm_apply_image
    (φ : RealSplitOctonionAut) (Γ : OperatorOneForm)
    (D : canonicalZornDerivations) :
    automorphismOneForm φ Γ (conjugateCanonicalDerivation φ D) =
      φ.1.conjAlgEquiv ℝ (Γ D) := by
  exact transportOneForm_apply_image _ _ _ _

/-- The concrete CE differential is equivariant under every existing
split-octonion automorphism. -/
theorem exteriorDerivativeOne_automorphism
    (φ : RealSplitOctonionAut) (Γ : OperatorOneForm)
    (D E : canonicalZornDerivations) :
    DerivationDifferentialForms.exteriorDerivativeOne Lane
        (automorphismOneForm φ Γ)
        (conjugateCanonicalDerivation φ D)
        (conjugateCanonicalDerivation φ E) =
      φ.1.conjAlgEquiv ℝ
        (DerivationDifferentialForms.exteriorDerivativeOne Lane Γ D E) := by
  exact exteriorDerivativeOne_transport (K := Lane) (K' := Lane)
    (conjugateCanonicalDerivation φ) (φ.1.conjAlgEquiv ℝ)
    (operatorAction_conjugate φ) Γ D E

/-- Arbitrary operator curvature transforms by the same native conjugation. -/
theorem connectionCurvature_automorphism
    (φ : RealSplitOctonionAut) (Γ : OperatorOneForm)
    (D E : canonicalZornDerivations) :
    DerivationDifferentialForms.connectionCurvature Lane
        (automorphismOneForm φ Γ)
        (conjugateCanonicalDerivation φ D)
        (conjugateCanonicalDerivation φ E) =
      φ.1.conjAlgEquiv ℝ
        (DerivationDifferentialForms.connectionCurvature Lane Γ D E) := by
  exact connectionCurvature_transport (K := Lane) (K' := Lane)
    (conjugateCanonicalDerivation φ) (φ.1.conjAlgEquiv ℝ)
    (operatorAction_conjugate φ) Γ D E

/-- The established canonical form `D ↦ -D` is fixed by this action. -/
theorem canonicalMaurerCartanForm_automorphism (φ : RealSplitOctonionAut) :
    automorphismOneForm φ canonicalMaurerCartanForm = canonicalMaurerCartanForm := by
  apply LinearMap.ext
  intro D
  change canonicalZornDerivations at D
  change φ.1.conjAlgEquiv ℝ
      (-((conjugateCanonicalDerivation φ).symm D).1) = -D.1
  rw [map_neg, ← conjugateCanonicalDerivation_val,
    LieEquiv.apply_symm_apply]

end InfoGeometry.OperatorAlgebra.CanonicalZornAutomorphismDifferentialForms
