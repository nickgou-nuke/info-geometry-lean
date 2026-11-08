/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionAutomorphismCore
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Algebra.ZornDerivationBridge
import Mathlib.Algebra.Group.Action.Basic

/-!
# Canonical split-octonion derivation conjugation

This is the existing conjugation block relocated from the G₂ root-coordinate
owner. Its public namespace and every declaration are unchanged. The group
acts on actual native derivations before any classification or root readout.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Canonical

noncomputable def nativeCanonicalVectorLinearEquiv :
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.CZ ≃ₗ[ℝ]
      ZornVectorMatrix ℝ :=
  { InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv with
    map_add' := by intro X Y; rfl
    map_smul' := by intro r X; rfl }

noncomputable def nativeAut (φ : RealSplitOctonionAut) :
    ZornVectorMatrix ℝ ≃ₗ[ℝ] ZornVectorMatrix ℝ :=
  nativeCanonicalVectorLinearEquiv.symm.trans
    (φ.1.trans nativeCanonicalVectorLinearEquiv)

theorem nativeAut_map_mul (φ : RealSplitOctonionAut)
    (X Y : ZornVectorMatrix ℝ) :
    nativeAut φ (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.mul (nativeAut φ X) (nativeAut φ Y) := by
  change canonicalVectorEquiv
      (φ.1 (canonicalVectorEquiv.symm
        (ZornVectorMatrix.mul X Y))) =
    ZornVectorMatrix.mul
      (canonicalVectorEquiv (φ.1 (canonicalVectorEquiv.symm X)))
      (canonicalVectorEquiv (φ.1 (canonicalVectorEquiv.symm Y)))
  rw [canonicalVectorEquiv_symm_mul, φ.2.2]
  simp only [canonicalVectorEquiv_mul]

theorem nativeAut_map_add (φ : RealSplitOctonionAut)
    (X Y : ZornVectorMatrix ℝ) :
    nativeAut φ (ZornVectorMatrix.add X Y) =
      ZornVectorMatrix.add (nativeAut φ X) (nativeAut φ Y) := by
  change canonicalVectorEquiv
      (φ.1 (canonicalVectorEquiv.symm
        (ZornVectorMatrix.add X Y))) =
    ZornVectorMatrix.add
      (canonicalVectorEquiv (φ.1 (canonicalVectorEquiv.symm X)))
      (canonicalVectorEquiv (φ.1 (canonicalVectorEquiv.symm Y)))
  rw [canonicalVectorEquiv_symm_add, map_add, canonicalVectorEquiv_add]

theorem nativeAut_map_smul (φ : RealSplitOctonionAut)
    (r : ℝ) (X : ZornVectorMatrix ℝ) :
    nativeAut φ (ZornVectorMatrix.smul r X) =
      ZornVectorMatrix.smul r (nativeAut φ X) := by
  change canonicalVectorEquiv
      (φ.1 (canonicalVectorEquiv.symm
        (ZornVectorMatrix.smul r X))) =
    ZornVectorMatrix.smul r
      (canonicalVectorEquiv (φ.1 (canonicalVectorEquiv.symm X)))
  rw [canonicalVectorEquiv_symm_smul, map_smul, canonicalVectorEquiv_smul]

theorem nativeAut_map_neg (φ : RealSplitOctonionAut)
    (X : ZornVectorMatrix ℝ) :
    nativeAut φ (ZornVectorMatrix.neg X) =
      ZornVectorMatrix.neg (nativeAut φ X) := by
  rw [ZornVectorMatrix.neg_eq_smul_neg_one, nativeAut_map_smul,
    ZornVectorMatrix.neg_eq_smul_neg_one]

theorem nativeAut_map_sub (φ : RealSplitOctonionAut)
    (X Y : ZornVectorMatrix ℝ) :
    nativeAut φ (ZornVectorMatrix.sub X Y) =
      ZornVectorMatrix.sub (nativeAut φ X) (nativeAut φ Y) := by
  rw [ZornVectorMatrix.sub_eq_add_neg, nativeAut_map_add,
    nativeAut_map_neg, ZornVectorMatrix.sub_eq_add_neg]

theorem nativeAut_map_sub' (φ : RealSplitOctonionAut)
    (X Y : ZornVectorMatrix ℝ) :
    nativeAut φ (X - Y) = nativeAut φ X - nativeAut φ Y := by
  exact nativeAut_map_sub φ X Y

theorem nativeAut_map_mul' (φ : RealSplitOctonionAut)
    (X Y : ZornVectorMatrix ℝ) :
    nativeAut φ (X * Y) = nativeAut φ X * nativeAut φ Y := by
  exact nativeAut_map_mul φ X Y

theorem nativeAut_map_add' (φ : RealSplitOctonionAut)
    (X Y : ZornVectorMatrix ℝ) :
    nativeAut φ (X + Y) = nativeAut φ X + nativeAut φ Y := by
  exact nativeAut_map_add φ X Y

theorem nativeAut_map_associator (φ : RealSplitOctonionAut)
    (X Y Z : ZornVectorMatrix ℝ) :
    nativeAut φ (_root_.associator X Y Z) =
      _root_.associator (nativeAut φ X) (nativeAut φ Y) (nativeAut φ Z) := by
  unfold _root_.associator
  change nativeAut φ (ZornVectorMatrix.sub (X * Y * Z) (X * (Y * Z))) =
    ZornVectorMatrix.sub
      (nativeAut φ X * nativeAut φ Y * nativeAut φ Z)
      (nativeAut φ X * (nativeAut φ Y * nativeAut φ Z))
  rw [nativeAut_map_sub φ, nativeAut_map_mul' φ (X * Y) Z,
    nativeAut_map_mul' φ X (Y * Z), nativeAut_map_mul' φ X Y,
    nativeAut_map_mul' φ Y Z]

theorem nativeAut_map_smul' (φ : RealSplitOctonionAut)
    (r : ℝ) (X : ZornVectorMatrix ℝ) :
    nativeAut φ (r • X) = r • nativeAut φ X := by
  exact nativeAut_map_smul φ r X

theorem nativeAut_one :
    nativeAut (1 : RealSplitOctonionAut) = LinearEquiv.refl ℝ _ := by
  apply LinearEquiv.ext
  intro X
  rfl

theorem nativeAut_mul (φ ψ : RealSplitOctonionAut) :
    nativeAut (φ * ψ) = nativeAut φ * nativeAut ψ := by
  apply LinearEquiv.ext
  intro X
  rfl

/-! Conjugation transports native derivations along a genuine split-octonion
automorphism.  This is the adjoint action before any root-coordinate readout. -/

def conjugateNativeDerivation (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ)) :
    ZornVectorMatrix.Derivation (R := ℝ) where
  toFun X := nativeAut φ (D ((nativeAut φ).symm X))
  map_add' X Y := by
    have h := (nativeAut φ).symm.map_add X Y
    change (nativeAut φ).symm (X + Y) =
      (nativeAut φ).symm X + (nativeAut φ).symm Y at h
    change nativeAut φ (D ((nativeAut φ).symm (X + Y))) = _
    calc
      nativeAut φ (D ((nativeAut φ).symm (X + Y))) =
          nativeAut φ (D ((nativeAut φ).symm X + (nativeAut φ).symm Y)) := by
            rw [h]
      _ = nativeAut φ (D ((nativeAut φ).symm X) +
            D ((nativeAut φ).symm Y)) := by
            congr 1
            exact D.map_add _ _
      _ = nativeAut φ (D ((nativeAut φ).symm X)) +
            nativeAut φ (D ((nativeAut φ).symm Y)) := by
            exact nativeAut_map_add φ _ _
  map_smul' r X := by
    have h := (nativeAut φ).symm.map_smul r X
    change (nativeAut φ).symm (r • X) = r • (nativeAut φ).symm X at h
    change nativeAut φ (D ((nativeAut φ).symm (r • X))) = _
    calc
      nativeAut φ (D ((nativeAut φ).symm (r • X))) =
          nativeAut φ (D (r • (nativeAut φ).symm X)) := by
            rw [h]
      _ = nativeAut φ (r • D ((nativeAut φ).symm X)) := by
            congr 1
            exact D.map_smul r _
      _ = r • nativeAut φ (D ((nativeAut φ).symm X)) := by
            exact nativeAut_map_smul φ _ _
  map_mul' X Y := by
    have hinv : (nativeAut φ).symm (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.mul ((nativeAut φ).symm X) ((nativeAut φ).symm Y) := by
      apply (nativeAut φ).injective
      rw [nativeAut_map_mul]
      simp
    rw [hinv]
    rw [D.map_mul]
    rw [nativeAut_map_add]
    have hleft := nativeAut_map_mul φ (D ((nativeAut φ).symm X))
      ((nativeAut φ).symm Y)
    have hright := nativeAut_map_mul φ ((nativeAut φ).symm X)
      (D ((nativeAut φ).symm Y))
    rw [hleft, hright]
    simp only [(nativeAut φ).apply_symm_apply]

theorem conjugateNativeDerivation_is_derivation
    (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ))
    (X Y : ZornVectorMatrix ℝ) :
    conjugateNativeDerivation φ D (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (conjugateNativeDerivation φ D X) Y)
        (ZornVectorMatrix.mul X (conjugateNativeDerivation φ D Y)) := by
  exact (conjugateNativeDerivation φ D).map_mul' X Y

instance : SMul RealSplitOctonionAut
    (ZornVectorMatrix.Derivation (R := ℝ)) where
  smul φ D := conjugateNativeDerivation φ D

instance : MulAction RealSplitOctonionAut
    (ZornVectorMatrix.Derivation (R := ℝ)) where
  one_smul D := by
    apply ZornVectorMatrix.Derivation.ext
    intro X
    change conjugateNativeDerivation (1 : RealSplitOctonionAut) D X = D X
    simp [conjugateNativeDerivation, nativeAut_one]
  mul_smul φ ψ D := by
    apply ZornVectorMatrix.Derivation.ext
    intro X
    change conjugateNativeDerivation (φ * ψ) D X =
      conjugateNativeDerivation φ (conjugateNativeDerivation ψ D) X
    simp only [conjugateNativeDerivation]
    have hinv : (nativeAut (φ * ψ)).symm X =
        (nativeAut ψ).symm ((nativeAut φ).symm X) := by
      rw [nativeAut_mul]
      rfl
    rw [hinv]
    rw [nativeAut_mul]
    rfl

/-! The adjoint action is linear on the native derivation carrier.  Packaging
it as a `LinearMap` is the interface required by the trace/character layer. -/

noncomputable def conjugateNativeDerivationLinear
    (φ : RealSplitOctonionAut) :
    ZornVectorMatrix.Derivation (R := ℝ) →ₗ[ℝ]
      ZornVectorMatrix.Derivation (R := ℝ) where
  toFun D := conjugateNativeDerivation φ D
  map_add' D E := by
    apply ZornVectorMatrix.Derivation.ext
    intro X
    change nativeAut φ
        (D ((nativeAut φ).symm X) + E ((nativeAut φ).symm X)) =
      nativeAut φ (D ((nativeAut φ).symm X)) +
        nativeAut φ (E ((nativeAut φ).symm X))
    rw [nativeAut_map_add']
  map_smul' r D := by
    apply ZornVectorMatrix.Derivation.ext
    intro X
    change nativeAut φ (r • D ((nativeAut φ).symm X)) =
      r • nativeAut φ (D ((nativeAut φ).symm X))
    rw [nativeAut_map_smul']

@[simp] theorem conjugateNativeDerivationLinear_apply
    (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ)) :
    conjugateNativeDerivationLinear φ D = conjugateNativeDerivation φ D := rfl

theorem conjugateNativeDerivation_map_lie
    (φ : RealSplitOctonionAut)
    (D E : ZornVectorMatrix.Derivation (R := ℝ)) :
    conjugateNativeDerivation φ ⁅D, E⁆ =
      ⁅conjugateNativeDerivation φ D, conjugateNativeDerivation φ E⁆ := by
  apply ZornVectorMatrix.Derivation.ext
  intro X
  change nativeAut φ
      (ZornVectorMatrix.Derivation.bracket D E ((nativeAut φ).symm X)) =
    ZornVectorMatrix.Derivation.bracket
      (conjugateNativeDerivation φ D)
      (conjugateNativeDerivation φ E) X
  simp only [ZornVectorMatrix.Derivation.bracket_apply,
    conjugateNativeDerivation]
  rw [nativeAut_map_sub]
  simp

theorem conjugateNativeDerivationLinear_comp_inv
    (φ : RealSplitOctonionAut) :
    (conjugateNativeDerivationLinear φ⁻¹).comp
        (conjugateNativeDerivationLinear φ) = LinearMap.id := by
  apply LinearMap.ext
  intro D
  change conjugateNativeDerivation φ⁻¹
      (conjugateNativeDerivation φ D) = D
  exact inv_smul_smul φ D

theorem conjugateNativeDerivationLinear_inv_comp
    (φ : RealSplitOctonionAut) :
    (conjugateNativeDerivationLinear φ).comp
        (conjugateNativeDerivationLinear φ⁻¹) = LinearMap.id := by
  apply LinearMap.ext
  intro D
  change conjugateNativeDerivation φ
      (conjugateNativeDerivation φ⁻¹ D) = D
  exact smul_inv_smul φ D

theorem conjugateNativeDerivationLinear_bijective
    (φ : RealSplitOctonionAut) :
    Function.Bijective (conjugateNativeDerivationLinear φ) := by
  constructor
  · intro D E h
    have h' := congrArg (conjugateNativeDerivationLinear φ⁻¹) h
    change conjugateNativeDerivation φ⁻¹
        (conjugateNativeDerivation φ D) =
      conjugateNativeDerivation φ⁻¹
        (conjugateNativeDerivation φ E) at h'
    calc
      D = conjugateNativeDerivation φ⁻¹
          (conjugateNativeDerivation φ D) := (inv_smul_smul φ D).symm
      _ = conjugateNativeDerivation φ⁻¹
          (conjugateNativeDerivation φ E) := h'
      _ = E := inv_smul_smul φ E
  · intro D
    refine ⟨conjugateNativeDerivationLinear φ⁻¹ D, ?_⟩
    change conjugateNativeDerivation φ
        (conjugateNativeDerivation φ⁻¹ D) = D
    exact smul_inv_smul φ D

noncomputable def conjugateNativeDerivationEquiv
    (φ : RealSplitOctonionAut) :
    ZornVectorMatrix.Derivation (R := ℝ) ≃ₗ[ℝ]
      ZornVectorMatrix.Derivation (R := ℝ) :=
  LinearEquiv.ofBijective (conjugateNativeDerivationLinear φ)
    (conjugateNativeDerivationLinear_bijective φ)

noncomputable def conjugateNativeDerivationLieEquiv
    (φ : RealSplitOctonionAut) :
    ZornVectorMatrix.Derivation (R := ℝ) ≃ₗ⁅ℝ⁆
      ZornVectorMatrix.Derivation (R := ℝ) :=
  { conjugateNativeDerivationEquiv φ with
    map_lie' := by
      intro D E
      exact conjugateNativeDerivation_map_lie φ D E }

noncomputable def conjugateCanonicalDerivation
    (φ : RealSplitOctonionAut) :
    InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations ≃ₗ⁅ℝ⁆
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.symm.trans
    ((conjugateNativeDerivationLieEquiv φ).trans
      InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv)

@[simp] theorem conjugateCanonicalDerivation_apply
    (φ : RealSplitOctonionAut)
    (D : InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations) :
    conjugateCanonicalDerivation φ D =
      InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv
          (conjugateNativeDerivation φ
          (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.symm D)) := rfl

end InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
