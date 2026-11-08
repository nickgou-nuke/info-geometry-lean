/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.Zorn.SplitOctonionDerivationConjugation
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornDerivationDimension
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Canonical.SplitOctonionAutomorphism
import InfoGeometry.Canonical.CanonicalChiralZornEquivariance
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Lie.CanonicalZornDerivationTrace
import InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear
import InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
import InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction

/-! The root-indexed part of the native characteristic-zero Zorn derivation carrier.

The finite `G2Root` model supplies the twelve labels.  The actual derivations are
the existing coordinate derivations of the Zorn product; this file only transports
the labels to those coordinates.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.CanonicalZornDerivationTrace
open InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCanonicalColorRootAction
open InfoGeometry.Algebra.Zorn.G2ChiralOperatorNativeBridge

noncomputable def parameterCanonicalLieEquiv :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.Params ≃ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.trans
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv.toLinearEquiv

def canonicalParameterSubmodule
    (P : Submodule ℝ InfoGeometry.Lie.CanonicalZornDerivationDimension.Params) :
    Submodule ℝ InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations :=
  P.map parameterCanonicalLieEquiv.toLinearMap

theorem mem_canonicalParameterSubmodule
    {P : Submodule ℝ InfoGeometry.Lie.CanonicalZornDerivationDimension.Params}
    {p : InfoGeometry.Lie.CanonicalZornDerivationDimension.Params}
    (hp : p ∈ P) :
    parameterCanonicalLieEquiv p ∈ canonicalParameterSubmodule P := by
  exact ⟨p, hp, rfl⟩

theorem conjugateCanonicalDerivation_parameterized
    (φ : RealSplitOctonionAut)
    (p : InfoGeometry.Lie.CanonicalZornDerivationDimension.Params) :
    conjugateCanonicalDerivation φ (parameterCanonicalLieEquiv p) =
      parameterCanonicalLieEquiv
        (InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters
          (conjugateNativeDerivation φ
            (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation p))) := by
  unfold conjugateCanonicalDerivation parameterCanonicalLieEquiv
  simp only [LieEquiv.trans_apply, LinearEquiv.trans_apply]
  change InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv
      (conjugateNativeDerivation φ (parameterDerivation p)) =
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv
      (parameterLinearEquiv
        (InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters
          (conjugateNativeDerivation φ (parameterDerivation p))))
  have h := InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterLinearEquiv.right_inv
    (conjugateNativeDerivation φ (parameterDerivation p))
  change parameterDerivation
      (InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters
        (conjugateNativeDerivation φ (parameterDerivation p))) = _ at h
  exact (congrArg InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLieEquiv h).symm

theorem conjugateCanonicalDerivation_mem_canonicalParameterSubmodule
    (φ : RealSplitOctonionAut)
    (P : Submodule ℝ InfoGeometry.Lie.CanonicalZornDerivationDimension.Params)
    (p : InfoGeometry.Lie.CanonicalZornDerivationDimension.Params)
    (hp : InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters
        (conjugateNativeDerivation φ
          (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation p)) ∈ P) :
    conjugateCanonicalDerivation φ (parameterCanonicalLieEquiv p) ∈
      canonicalParameterSubmodule P := by
  rw [conjugateCanonicalDerivation_parameterized]
  exact ⟨_, hp, rfl⟩

noncomputable def conjugatedParameterLieEquiv
    (φ : RealSplitOctonionAut) :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.Params ≃ₗ[ℝ]
      InfoGeometry.Lie.CanonicalZornDerivationDimension.Params :=
  parameterCanonicalLieEquiv.trans
    ((conjugateCanonicalDerivation φ).toLinearEquiv.trans
      parameterCanonicalLieEquiv.symm)

@[simp] theorem conjugatedParameterLieEquiv_apply
    (φ : RealSplitOctonionAut)
    (p : InfoGeometry.Lie.CanonicalZornDerivationDimension.Params) :
    conjugatedParameterLieEquiv φ p =
      InfoGeometry.Lie.CanonicalZornDerivationDimension.derivationParameters
        (conjugateNativeDerivation φ
          (InfoGeometry.Lie.CanonicalZornDerivationDimension.parameterDerivation p)) := by
  unfold conjugatedParameterLieEquiv
  simp only [LinearEquiv.trans_apply]
  change parameterCanonicalLieEquiv.symm
      (conjugateCanonicalDerivation φ (parameterCanonicalLieEquiv p)) = _
  rw [conjugateCanonicalDerivation_parameterized]
  exact parameterCanonicalLieEquiv.symm_apply_apply _

theorem conjugatedParameterLieEquiv_map_eq_of_map_le
    (φ : RealSplitOctonionAut)
    (P : Submodule ℝ Params)
    (hP : P.map (conjugatedParameterLieEquiv φ).toLinearMap ≤ P) :
    P.map (conjugatedParameterLieEquiv φ).toLinearMap = P := by
  apply Submodule.eq_of_le_of_finrank_eq hP
  exact (conjugatedParameterLieEquiv φ).finrank_map_eq P


@[simp] theorem conjugateNativeDerivationEquiv_apply
    (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ)) :
    conjugateNativeDerivationEquiv φ D = conjugateNativeDerivation φ D := rfl

theorem conjugateNative_innerDerivation
    (φ : RealSplitOctonionAut) (x y : ZornVectorMatrix ℝ) :
    conjugateNativeDerivation φ
        (InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation x y) =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeAut φ x) (nativeAut φ y) := by
  apply ZornVectorMatrix.Derivation.ext
  intro z
  change nativeAut φ
      (stanDerMap (R := ℝ) x y ((nativeAut φ).symm z)) =
    stanDerMap (R := ℝ) (nativeAut φ x) (nativeAut φ y) z
  rw [stanDerMap_apply_normal_form (zorn_left_alternative)
      (zorn_right_alternative),
    stanDerMap_apply_normal_form (zorn_left_alternative)
      (zorn_right_alternative)]
  have hcomm :
      nativeAut φ (x * y - y * x) =
        nativeAut φ x * nativeAut φ y - nativeAut φ y * nativeAut φ x := by
    calc
      nativeAut φ (x * y - y * x) =
          nativeAut φ (x * y) - nativeAut φ (y * x) :=
        nativeAut_map_sub' φ (x * y) (y * x)
      _ = nativeAut φ x * nativeAut φ y - nativeAut φ y * nativeAut φ x := by
        rw [nativeAut_map_mul', nativeAut_map_mul']
  have hassoc :
      nativeAut φ (_root_.associator x y ((nativeAut φ).symm z)) =
        _root_.associator (nativeAut φ x) (nativeAut φ y) z := by
    calc
      nativeAut φ (_root_.associator x y ((nativeAut φ).symm z)) =
          _root_.associator (nativeAut φ x) (nativeAut φ y)
            (nativeAut φ ((nativeAut φ).symm z)) :=
        nativeAut_map_associator φ x y ((nativeAut φ).symm z)
      _ = _root_.associator (nativeAut φ x) (nativeAut φ y) z := by
        rw [LinearEquiv.apply_symm_apply]
  calc
    nativeAut φ
        (((x * y - y * x) * (nativeAut φ).symm z -
          (nativeAut φ).symm z * (x * y - y * x)) -
          3 • _root_.associator x y ((nativeAut φ).symm z)) =
      nativeAut φ
          ((x * y - y * x) * (nativeAut φ).symm z -
            (nativeAut φ).symm z * (x * y - y * x)) -
        nativeAut φ (3 • _root_.associator x y ((nativeAut φ).symm z)) := by
          exact nativeAut_map_sub' φ _ _
    _ = ((nativeAut φ x * nativeAut φ y - nativeAut φ y * nativeAut φ x) * z -
          z * (nativeAut φ x * nativeAut φ y - nativeAut φ y * nativeAut φ x)) -
        3 • _root_.associator (nativeAut φ x) (nativeAut φ y) z := by
          rw [nativeAut_map_sub' φ _ _, nativeAut_map_mul' φ,
            nativeAut_map_mul' φ, hcomm,
            show nativeAut φ (3 • _root_.associator x y ((nativeAut φ).symm z)) =
              3 • nativeAut φ (_root_.associator x y ((nativeAut φ).symm z)) from
              map_nsmul (nativeAut φ) 3 _, hassoc]
          simp

theorem conjugateNativeDerivation_mem_innerPairSpan
    (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ))
    (hD : D ∈ Submodule.span ℝ (Set.range
      (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          p.1 p.2))) :
    conjugateNativeDerivation φ D ∈ Submodule.span ℝ (Set.range
      (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          p.1 p.2)) := by
  let S : Submodule ℝ (ZornVectorMatrix.Derivation (R := ℝ)) :=
    Submodule.span ℝ (Set.range
      (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          p.1 p.2))
  change conjugateNativeDerivation φ D ∈ S
  change D ∈ S at hD
  have hzero : conjugateNativeDerivation φ (0 : ZornVectorMatrix.Derivation (R := ℝ)) = 0 := by
    apply ZornVectorMatrix.Derivation.ext
    intro X
    change nativeAut φ 0 = 0
    exact (nativeAut φ).map_zero
  have hadd (E F : ZornVectorMatrix.Derivation (R := ℝ)) :
      conjugateNativeDerivation φ (E + F) =
        conjugateNativeDerivation φ E + conjugateNativeDerivation φ F := by
    apply ZornVectorMatrix.Derivation.ext
    intro X
    change nativeAut φ
        (E ((nativeAut φ).symm X) + F ((nativeAut φ).symm X)) =
      nativeAut φ (E ((nativeAut φ).symm X)) +
        nativeAut φ (F ((nativeAut φ).symm X))
    rw [nativeAut_map_add']
  have hsmul (r : ℝ) (E : ZornVectorMatrix.Derivation (R := ℝ)) :
      conjugateNativeDerivation φ (r • E) =
        r • conjugateNativeDerivation φ E := by
    apply ZornVectorMatrix.Derivation.ext
    intro X
    change nativeAut φ
        (r • E ((nativeAut φ).symm X)) =
      r • nativeAut φ (E ((nativeAut φ).symm X))
    rw [nativeAut_map_smul']
  refine Submodule.span_induction (p := fun E _ =>
    conjugateNativeDerivation φ E ∈ S) ?_ ?_ ?_ ?_ hD
  · intro E hE
    rcases hE with ⟨⟨x, y⟩, rfl⟩
    rw [conjugateNative_innerDerivation]
    exact Submodule.subset_span ⟨(nativeAut φ x, nativeAut φ y), rfl⟩
  · change conjugateNativeDerivation φ 0 ∈ S
    rw [hzero]
    exact S.zero_mem
  · intro E F _ _ hE hF
    rw [hadd]
    exact S.add_mem hE hF
  · intro r E _ hE
    rw [hsmul]
    exact S.smul_mem r hE

/-! Conjugation preserves the pair-generated derivation sector in both
directions.  The reverse implication is obtained from the inverse
automorphism, so this theorem does not require a root-coordinate sign choice. -/

theorem conjugateNativeDerivation_mem_innerPairSpan_iff
    (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ)) :
    conjugateNativeDerivation φ D ∈ Submodule.span ℝ (Set.range
      (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          p.1 p.2)) ↔
      D ∈ Submodule.span ℝ (Set.range
        (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
          InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
            p.1 p.2)) := by
  constructor
  · intro hD
    have h := conjugateNativeDerivation_mem_innerPairSpan φ⁻¹
      (conjugateNativeDerivation φ D) hD
    have hinv : conjugateNativeDerivation φ⁻¹
        (conjugateNativeDerivation φ D) = D := by
      change φ⁻¹ • (φ • D) = D
      exact inv_smul_smul φ D
    rw [hinv] at h
    exact h
  · exact conjugateNativeDerivation_mem_innerPairSpan φ D

/-
theorem conjugateNative_innerDerivation
    (φ : RealSplitOctonionAut) (x y : ZornVectorMatrix ℝ) :
    conjugateNativeDerivation φ
        (InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation x y) =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeAut φ x) (nativeAut φ y) := by
  apply ZornVectorMatrix.Derivation.ext
  intro z
  change nativeAut φ
      (stanDerMap (R := ℝ) x y ((nativeAut φ).symm z)) =
    stanDerMap (R := ℝ) (nativeAut φ x) (nativeAut φ y) z
  rw [stanDerMap_apply_normal_form (zorn_left_alternative)
      (zorn_right_alternative),
    stanDerMap_apply_normal_form (zorn_left_alternative)
      (zorn_right_alternative)]
  have hneg (A : ZornVectorMatrix ℝ) :
      nativeAut φ (-A) = -nativeAut φ A := by
    change nativeAut φ (ZornVectorMatrix.neg A) =
      ZornVectorMatrix.neg (nativeAut φ A)
    rw [ZornVectorMatrix.neg_eq_smul_neg_one, nativeAut_map_smul,
      ZornVectorMatrix.neg_eq_smul_neg_one]
    rfl
  have hcomm :
      nativeAut φ (x * y - y * x) =
        nativeAut φ x * nativeAut φ y - nativeAut φ y * nativeAut φ x := by
    change nativeAut φ
        (ZornVectorMatrix.sub (ZornVectorMatrix.mul x y)
          (ZornVectorMatrix.mul y x)) = _
    rw [show ZornVectorMatrix.sub (ZornVectorMatrix.mul x y)
          (ZornVectorMatrix.mul y x) =
        ZornVectorMatrix.add (ZornVectorMatrix.mul x y)
          (-ZornVectorMatrix.mul y x) by rfl]
    rw [nativeAut_map_add, hneg, nativeAut_map_mul, nativeAut_map_mul]
    rfl
  have hassoc : nativeAut φ (_root_.associator x y ((nativeAut φ).symm z)) =
      _root_.associator (nativeAut φ x) (nativeAut φ y) z := by
    change nativeAut φ
        (ZornVectorMatrix.sub
          (ZornVectorMatrix.mul (ZornVectorMatrix.mul x y)
            ((nativeAut φ).symm z))
          (ZornVectorMatrix.mul x
            (ZornVectorMatrix.mul y ((nativeAut φ).symm z)))) = _
    rw [show ZornVectorMatrix.sub
          (ZornVectorMatrix.mul (ZornVectorMatrix.mul x y)
            ((nativeAut φ).symm z))
          (ZornVectorMatrix.mul x
            (ZornVectorMatrix.mul y ((nativeAut φ).symm z))) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (ZornVectorMatrix.mul x y)
            ((nativeAut φ).symm z))
          (-ZornVectorMatrix.mul x
            (ZornVectorMatrix.mul y ((nativeAut φ).symm z))) by rfl]
    rw [nativeAut_map_add, hneg, nativeAut_map_mul, nativeAut_map_mul,
      nativeAut_map_mul]
    simp
    rfl
  rw [hcomm, nativeAut_map_mul, nativeAut_map_mul, hassoc]
  simp
-/

/-! Real representatives of the two canonical colour symmetries.  These are
the genuine characteristic-zero lifts of the canonical composition
automorphisms; no identification with the finite `SplitOctF2Aut` carrier is
asserted here. -/

noncomputable def realWeylCycle : RealSplitOctonionAut :=
  { val := InfoGeometry.Canonical.canonicalColorCycleCompositionAut.1
    property := by
      constructor
      · exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_fix_one
          InfoGeometry.Canonical.canonicalColorCycleCompositionAut
      · intro X Y
        exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_mul
          InfoGeometry.Canonical.canonicalColorCycleCompositionAut X Y }

noncomputable def realWeylReflection : RealSplitOctonionAut :=
  { val := InfoGeometry.Canonical.canonicalColorReflectionCompositionAut.1
    property := by
      constructor
      · exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_fix_one
          InfoGeometry.Canonical.canonicalColorReflectionCompositionAut
      · intro X Y
        exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_mul
          InfoGeometry.Canonical.canonicalColorReflectionCompositionAut X Y }

theorem realWeylCycle_nativeCircularBasis (i : Fin 8) :
    nativeAut realWeylCycle (nativeCircularBasis i) =
      nativeCircularBasis (cycleFrameIndex i) := by
  change canonicalVectorEquiv
      (canonicalColorCycle
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i)) =
    nativeCircularBasis (cycleFrameIndex i)
  exact canonicalColorCycle_nativeCircularBasis i

theorem realWeylReflection_nativeCircularBasis (i : Fin 8) :
    nativeAut realWeylReflection (nativeCircularBasis i) =
      nativeCircularBasis (reflectionFrameIndex i) := by
  change canonicalVectorEquiv
      (canonicalColorReflection
        (InfoGeometry.Lie.SplitOctonionCircularPeirceBasis.circularPeirceBasis i)) =
    nativeCircularBasis (reflectionFrameIndex i)
  exact canonicalColorReflection_nativeCircularBasis i

theorem cycleFrameIndex_bijective :
    Function.Bijective cycleFrameIndex := by
  decide

theorem reflectionFrameIndex_bijective :
    Function.Bijective reflectionFrameIndex := by
  decide

@[simp] theorem realWeylCycle_apply (X : SplitOctonionReal) :
    (realWeylCycle : SplitOctonionAutCandidate ℝ) X =
      (InfoGeometry.Canonical.canonicalColorCycleCompositionAut :
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X := rfl

@[simp] theorem realWeylReflection_apply (X : SplitOctonionReal) :
    (realWeylReflection : SplitOctonionAutCandidate ℝ) X =
      (InfoGeometry.Canonical.canonicalColorReflectionCompositionAut :
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) X := rfl

theorem realWeylCycle_adjoint_is_derivation
    (D : ZornVectorMatrix.Derivation (R := ℝ))
    (X Y : ZornVectorMatrix ℝ) :
    conjugateNativeDerivation realWeylCycle D (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul (conjugateNativeDerivation realWeylCycle D X) Y)
        (ZornVectorMatrix.mul X (conjugateNativeDerivation realWeylCycle D Y)) := by
  exact conjugateNativeDerivation_is_derivation realWeylCycle D X Y

theorem realWeylReflection_adjoint_is_derivation
    (D : ZornVectorMatrix.Derivation (R := ℝ))
    (X Y : ZornVectorMatrix ℝ) :
    conjugateNativeDerivation realWeylReflection D (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.add
        (ZornVectorMatrix.mul
          (conjugateNativeDerivation realWeylReflection D X) Y)
        (ZornVectorMatrix.mul X
          (conjugateNativeDerivation realWeylReflection D Y)) := by
  exact conjugateNativeDerivation_is_derivation realWeylReflection D X Y

theorem realWeylCycle_innerDerivation_covariant
    (x y : ZornVectorMatrix ℝ) :
    realWeylCycle •
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation x y =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeAut realWeylCycle x) (nativeAut realWeylCycle y) := by
  exact conjugateNative_innerDerivation realWeylCycle x y

theorem realWeylReflection_innerDerivation_covariant
    (x y : ZornVectorMatrix ℝ) :
    realWeylReflection •
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation x y =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeAut realWeylReflection x) (nativeAut realWeylReflection y) := by
  exact conjugateNative_innerDerivation realWeylReflection x y

theorem realWeylCycle_nativeCircularPairDerivation
    (i j : Fin 8) :
    realWeylCycle •
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          (nativeCircularBasis i) (nativeCircularBasis j) =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (cycleFrameIndex i))
        (nativeCircularBasis (cycleFrameIndex j)) := by
  rw [realWeylCycle_innerDerivation_covariant,
    realWeylCycle_nativeCircularBasis,
    realWeylCycle_nativeCircularBasis]

theorem realWeylReflection_nativeCircularPairDerivation
    (i j : Fin 8) :
    realWeylReflection •
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          (nativeCircularBasis i) (nativeCircularBasis j) =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (reflectionFrameIndex i))
        (nativeCircularBasis (reflectionFrameIndex j)) := by
  rw [realWeylReflection_innerDerivation_covariant,
    realWeylReflection_nativeCircularBasis,
    realWeylReflection_nativeCircularBasis]

theorem realWeylCycle_nativeCircularPairSet_image :
    (fun D : ZornVectorMatrix.Derivation (R := ℝ) => realWeylCycle • D) ''
        Set.range (fun p : Fin 8 × Fin 8 =>
          InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
            (nativeCircularBasis p.1) (nativeCircularBasis p.2)) =
      Set.range (fun p : Fin 8 × Fin 8 =>
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          (nativeCircularBasis p.1) (nativeCircularBasis p.2)) := by
  ext D
  constructor
  · rintro ⟨E, ⟨⟨i, j⟩, rfl⟩, rfl⟩
    exact ⟨(cycleFrameIndex i, cycleFrameIndex j),
      (realWeylCycle_nativeCircularPairDerivation i j).symm⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    rcases cycleFrameIndex_bijective.2 i with ⟨i', hi'⟩
    rcases cycleFrameIndex_bijective.2 j with ⟨j', hj'⟩
    refine ⟨InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
      (nativeCircularBasis i') (nativeCircularBasis j'),
      ⟨(i', j'), rfl⟩, ?_⟩
    change realWeylCycle •
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          (nativeCircularBasis i') (nativeCircularBasis j') =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis i) (nativeCircularBasis j)
    rw [realWeylCycle_nativeCircularPairDerivation, hi', hj']

theorem realWeylReflection_nativeCircularPairSet_image :
    (fun D : ZornVectorMatrix.Derivation (R := ℝ) => realWeylReflection • D) ''
        Set.range (fun p : Fin 8 × Fin 8 =>
          InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
            (nativeCircularBasis p.1) (nativeCircularBasis p.2)) =
      Set.range (fun p : Fin 8 × Fin 8 =>
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          (nativeCircularBasis p.1) (nativeCircularBasis p.2)) := by
  ext D
  constructor
  · rintro ⟨E, ⟨⟨i, j⟩, rfl⟩, rfl⟩
    exact ⟨(reflectionFrameIndex i, reflectionFrameIndex j),
      (realWeylReflection_nativeCircularPairDerivation i j).symm⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    rcases reflectionFrameIndex_bijective.2 i with ⟨i', hi'⟩
    rcases reflectionFrameIndex_bijective.2 j with ⟨j', hj'⟩
    refine ⟨InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
      (nativeCircularBasis i') (nativeCircularBasis j'),
      ⟨(i', j'), rfl⟩, ?_⟩
    change realWeylReflection •
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          (nativeCircularBasis i') (nativeCircularBasis j') =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis i) (nativeCircularBasis j)
    rw [realWeylReflection_nativeCircularPairDerivation, hi', hj']

theorem realWeylCycle_chiralReadoutBasis
    (g : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    nativeAut realWeylCycle (chiralReadoutBasis g) =
      nativeCircularBasis (cycleFrameIndex (chiralGeneratorIndex g)) := by
  rw [chiralReadoutBasis_eq_nativeCircularBasis,
    show chiralNativeBasis g =
      nativeCircularBasis (chiralGeneratorIndex g) by
        rfl]
  exact realWeylCycle_nativeCircularBasis (chiralGeneratorIndex g)

theorem realWeylReflection_chiralReadoutBasis
    (g : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    nativeAut realWeylReflection (chiralReadoutBasis g) =
      nativeCircularBasis (reflectionFrameIndex (chiralGeneratorIndex g)) := by
  rw [chiralReadoutBasis_eq_nativeCircularBasis,
    show chiralNativeBasis g =
      nativeCircularBasis (chiralGeneratorIndex g) by
        rfl]
  exact realWeylReflection_nativeCircularBasis (chiralGeneratorIndex g)

theorem realWeylCycle_chiralReadoutPairDerivation
    (g h : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    realWeylCycle •
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          (chiralReadoutBasis g) (chiralReadoutBasis h) =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (cycleFrameIndex (chiralGeneratorIndex g)))
        (nativeCircularBasis (cycleFrameIndex (chiralGeneratorIndex h))) := by
  rw [chiralReadoutBasis_eq_nativeCircularBasis,
    chiralReadoutBasis_eq_nativeCircularBasis]
  change realWeylCycle •
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (chiralGeneratorIndex g))
        (nativeCircularBasis (chiralGeneratorIndex h)) = _
  exact realWeylCycle_nativeCircularPairDerivation
    (chiralGeneratorIndex g) (chiralGeneratorIndex h)

theorem realWeylReflection_chiralReadoutPairDerivation
    (g h : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    realWeylReflection •
        InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
          (chiralReadoutBasis g) (chiralReadoutBasis h) =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (reflectionFrameIndex (chiralGeneratorIndex g)))
        (nativeCircularBasis (reflectionFrameIndex (chiralGeneratorIndex h))) := by
  rw [chiralReadoutBasis_eq_nativeCircularBasis,
    chiralReadoutBasis_eq_nativeCircularBasis]
  change realWeylReflection •
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeCircularBasis (chiralGeneratorIndex g))
        (nativeCircularBasis (chiralGeneratorIndex h)) = _
  exact realWeylReflection_nativeCircularPairDerivation
    (chiralGeneratorIndex g) (chiralGeneratorIndex h)

instance : Fintype RootLength where
  elems := {RootLength.Short, RootLength.Long}
  complete := by
    intro r
    cases r <;> simp

def zmod6Fin (k : ZMod 6) : Fin 6 :=
  ⟨k.val, k.val_lt⟩

def rootCoordinate : G2Root → Fin 14 := fun r =>
  match r.1 with
  | RootLength.Short => ![0, 3, 4, 8, 9, 10] (zmod6Fin r.2)
  | RootLength.Long  => ![1, 2, 5, 7, 11, 12] (zmod6Fin r.2)

def zornDerivationRootRepresentation (r : G2Root) :
    ZornVectorMatrix.Derivation (R := ℝ) :=
  parameterDerivation (fun i => if i = rootCoordinate r then 1 else 0)

theorem zornDerivationRootRepresentation_is_derivation (r : G2Root) :
    ∀ X Y : ZornVectorMatrix ℝ,
      zornDerivationRootRepresentation r (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (zornDerivationRootRepresentation r X) Y)
          (ZornVectorMatrix.mul X (zornDerivationRootRepresentation r Y)) := by
  intro X Y
  exact (zornDerivationRootRepresentation r).map_mul' X Y

theorem rootCoordinate_injective : Function.Injective rootCoordinate := by
  decide

theorem zornDerivationRootRepresentation_injective :
    Function.Injective zornDerivationRootRepresentation := by
  intro r s h
  apply rootCoordinate_injective
  have hp : (fun i => if i = rootCoordinate r then (1 : ℝ) else 0) =
      (fun i => if i = rootCoordinate s then (1 : ℝ) else 0) := by
    have h' := congrArg parameterLinearEquiv.symm h
    change derivationParameters (parameterDerivation
        (fun i => if i = rootCoordinate r then 1 else 0)) =
      derivationParameters (parameterDerivation
        (fun i => if i = rootCoordinate s then 1 else 0)) at h'
    calc
      (fun i => if i = rootCoordinate r then 1 else 0) =
          derivationParameters (parameterDerivation
            (fun i => if i = rootCoordinate r then 1 else 0)) :=
        (parameterLinearEquiv.left_inv _).symm
      _ = derivationParameters (parameterDerivation
            (fun i => if i = rootCoordinate s then 1 else 0)) := h'
      _ = (fun i => if i = rootCoordinate s then 1 else 0) :=
        parameterLinearEquiv.left_inv _
  by_contra hrs
  have hcoord := congrFun hp (rootCoordinate r)
  simp [hrs] at hcoord

theorem zornDerivationRootRepresentation_map_smul (r : G2Root) (a : ℝ) (X : ZornVectorMatrix ℝ) :
    zornDerivationRootRepresentation r (ZornVectorMatrix.smul a X) =
      ZornVectorMatrix.smul a (zornDerivationRootRepresentation r X) :=
  (zornDerivationRootRepresentation r).map_smul' a X

def nativeParameterBasis (j : Fin 14) : ZornVectorMatrix.Derivation (R := ℝ) :=
  parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) j)

theorem nativeParameterBasis_span :
    Submodule.span ℝ (Set.range nativeParameterBasis) = ⊤ := by
  let b := (Pi.basisFun ℝ (Fin 14)).map parameterLinearEquiv
  change Submodule.span ℝ (Set.range b) = ⊤
  exact b.span_eq

def cartanDerivation (j : Fin 2) : ZornVectorMatrix.Derivation (R := ℝ) :=
  nativeParameterBasis (![6, 13] j)

theorem rootRepresentation_eq_nativeParameterBasis (r : G2Root) :
    zornDerivationRootRepresentation r = nativeParameterBasis (rootCoordinate r) := by
  change parameterLinearEquiv
      (fun i => if i = rootCoordinate r then 1 else 0) =
    parameterLinearEquiv (Pi.basisFun ℝ (Fin 14) (rootCoordinate r))
  rw [show (fun i => if i = rootCoordinate r then 1 else 0) =
      Pi.basisFun ℝ (Fin 14) (rootCoordinate r) by
        ext i
        simp [Pi.basisFun, Pi.single_apply]]

theorem cartanDerivation_eq_nativeParameterBasis (j : Fin 2) :
    cartanDerivation j = nativeParameterBasis (![6, 13] j) := rfl

theorem cartan_root_span_eq_top :
    Submodule.span ℝ
        (Set.range cartanDerivation ∪ Set.range zornDerivationRootRepresentation) = ⊤ := by
  have hset : Set.range cartanDerivation ∪ Set.range zornDerivationRootRepresentation =
      Set.range nativeParameterBasis := by
    ext D
    constructor
    · intro h
      rcases h with h | h
      · rcases h with ⟨j, rfl⟩
        exact ⟨![6, 13] j, rfl⟩
      · rcases h with ⟨r, rfl⟩
        exact ⟨rootCoordinate r, (rootRepresentation_eq_nativeParameterBasis r).symm⟩
    · rintro ⟨j, rfl⟩
      fin_cases j
      all_goals
        first
        | exact Or.inl ⟨0, rfl⟩
        | exact Or.inl ⟨1, rfl⟩
        | exact Or.inr ⟨(RootLength.Short, 0), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Short, 1), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Short, 2), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Short, 3), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Short, 4), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Short, 5), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Long, 0), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Long, 1), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Long, 2), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Long, 3), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Long, 4), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
        | exact Or.inr ⟨(RootLength.Long, 5), by
            rw [rootRepresentation_eq_nativeParameterBasis]
            rfl⟩
  rw [hset]
  exact nativeParameterBasis_span

/-! The root-span owner ends here.  Conjugation transport belongs to the
native automorphism owners, where multiplication preservation is available.

The native transport below is the adjoint action on the existing derivation
carrier; the root-coordinate declarations above remain its label interface.

-/

/-
def nativeAut (φ : RealSplitOctonionAut) :
    ZornVectorMatrix ℝ ≃ₗ[ℝ] ZornVectorMatrix ℝ where
  toFun := (canonicalVectorEquiv.symm.trans φ.1).trans canonicalVectorEquiv
  invFun := (canonicalVectorEquiv.symm.trans φ.1.symm).trans canonicalVectorEquiv
  left_inv X := by simp
  right_inv X := by simp
  map_add' X Y := by
    simp
  map_smul' a X := by
    simp

theorem nativeAut_map_mul (φ : RealSplitOctonionAut) (X Y : ZornVectorMatrix ℝ) :
    nativeAut φ (ZornVectorMatrix.mul X Y) =
      ZornVectorMatrix.mul (nativeAut φ X) (nativeAut φ Y) := by
  simp [nativeAut, RealSplitOctonionAut.preserves_mul]

theorem nativeAut_one : nativeAut (1 : RealSplitOctonionAut) = LinearEquiv.refl ℝ _ := by
  apply LinearEquiv.ext
  intro X
  rfl

theorem nativeAut_mul (φ ψ : RealSplitOctonionAut) :
    nativeAut (φ * ψ) = nativeAut φ * nativeAut ψ := by
  apply LinearEquiv.ext
  intro X
  rfl

def conjugateNativeDerivation (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ)) :
    ZornVectorMatrix.Derivation (R := ℝ) where
  toFun X := nativeAut φ (D ((nativeAut φ).symm X))
  map_add' X Y := by
    simp [nativeAut, ZornVectorMatrix.add]
  map_smul' a X := by
    simp [nativeAut, ZornVectorMatrix.smul]
  map_mul' X Y := by
    rw [show (nativeAut φ).symm (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.mul ((nativeAut φ).symm X) ((nativeAut φ).symm Y) by
          apply (nativeAut φ).injective
          rw [nativeAut_map_mul]
          simp]
    rw [(D.map_mul' _ _)]
    rw [← (nativeAut φ).map_add]
    congr 1
    · rw [nativeAut_map_mul]
    · rw [nativeAut_map_mul]

theorem conjugateNativeDerivation_is_derivation
    (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ)) :
    ∀ X Y : ZornVectorMatrix ℝ,
      conjugateNativeDerivation φ D (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add
          (ZornVectorMatrix.mul (conjugateNativeDerivation φ D X) Y)
          (ZornVectorMatrix.mul X (conjugateNativeDerivation φ D Y)) := by
  intro X Y
  exact (conjugateNativeDerivation φ D).map_mul' X Y

theorem conjugateNativeStanDerivation_apply
    (φ : RealSplitOctonionAut) (x y z : ZornVectorMatrix ℝ) :
    conjugateNativeDerivation φ
        (fromNonAssocDerivation (zornStanDerivation x y)) z =
      fromNonAssocDerivation
        (zornStanDerivation (nativeAut φ x) (nativeAut φ y)) z := by
  change nativeAut φ
      (stanDerMap (R := ℝ) x y ((nativeAut φ).symm z)) =
    stanDerMap (R := ℝ) (nativeAut φ x) (nativeAut φ y) z
  rw [stanDerMap_apply_normal_form, stanDerMap_apply_normal_form]
  have hcomm :
      nativeAut φ (x * y - y * x) =
        nativeAut φ x * nativeAut φ y - nativeAut φ y * nativeAut φ x := by
    rw [map_sub, nativeAut_map_mul, nativeAut_map_mul]
  have hassoc :
      nativeAut φ (ZornVectorMatrix.associator x y ((nativeAut φ).symm z)) =
        ZornVectorMatrix.associator (nativeAut φ x) (nativeAut φ y) z := by
    unfold ZornVectorMatrix.associator
    rw [map_sub, nativeAut_map_mul, nativeAut_map_mul,
      nativeAut_map_mul]
    simp
  rw [hcomm, nativeAut_map_mul, nativeAut_map_mul, hassoc]
  simp

theorem conjugateNative_innerDerivation
    (φ : RealSplitOctonionAut) (x y : ZornVectorMatrix ℝ) :
    conjugateNativeDerivation φ
        (InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation x y) =
      InfoGeometry.Algebra.Zorn.NativeStanDerivationBilinear.innerDerivation
        (nativeAut φ x) (nativeAut φ y) := by
  apply ZornVectorMatrix.Derivation.ext
  intro z
  exact conjugateNativeStanDerivation_apply φ x y z

instance : SMul RealSplitOctonionAut
    (ZornVectorMatrix.Derivation (R := ℝ)) where
  smul φ D := conjugateNativeDerivation φ D

instance : MulAction RealSplitOctonionAut
    (ZornVectorMatrix.Derivation (R := ℝ)) where
  one_smul D := by
    apply DFunLike.ext _ _
    intro X
    simp [HSMul.hSMul, conjugateNativeDerivation, nativeAut_one]
  mul_smul φ ψ D := by
    apply DFunLike.ext _ _
    intro X
    simp [HSMul.hSMul, conjugateNativeDerivation, nativeAut_mul,
      LinearEquiv.mul_apply]

theorem autAdjointAction_is_derivation
    (φ : RealSplitOctonionAut)
    (D : ZornVectorMatrix.Derivation (R := ℝ)) :
    ∀ X Y : ZornVectorMatrix ℝ,
      (φ • D) (ZornVectorMatrix.mul X Y) =
        ZornVectorMatrix.add ((φ • D) X |> fun Z => ZornVectorMatrix.mul Z Y)
          (ZornVectorMatrix.mul X ((φ • D) Y)) := by
  intro X Y
  exact (φ • D).map_mul' X Y

/-! The circular Peirce basis is a basis of the eight-dimensional Zorn
carrier, not of the fourteen-dimensional derivation carrier.  This negative
dimension check prevents an accidental identification by index names. -/

theorem no_linearEquiv_circularCoordinates_to_nativeDerivations :
    ¬ Nonempty
      (CartesianCoordinates ≃ₗ[ℝ]
        ZornVectorMatrix.Derivation (R := ℝ)) := by
  rintro ⟨e⟩
  have h := e.finrank_eq
  rw [cartesianCoordinates_finrank, finrank_vectorDerivations] at h
  norm_num at h


-/
end InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
