/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealCl55NativeChiralSectorBridge

/-!
# Native chiral Hodge arrows and the finite index firewall

This owner restricts the existing native chiral Dirac blocks to the two
projector sectors and packages the scalar-square theorem
`D_- D_+ = 3 P_+`, `D_+ D_- = 3 P_-` as inverse and index-zero results.
It is a finite-dimensional algebraic statement only; it does not define an
analytic Fredholm index, a Kasparov class, or a group-level equivariant index.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeChiralHodgeIndexBridge

open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.RealCl55NativeChiralSectorBridge
open InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge
open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge

variable {G : Type*} [Group G]

theorem nativeChiralDiracMinusArrow_comp_plusArrow_apply
    (x : nativePlusSector) :
    nativeChiralDiracMinusArrow (nativeChiralDiracPlusArrow x) =
      (3 : ℝ) • x := by
  apply Subtype.ext
  have h := congrArg
    (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
    nativeChiralLaplacianPlus_eq_three_projector
  change nativeChiralDiracMinus (nativeChiralDiracPlus x.1) =
    (3 : ℝ) • nativeChiralProjectorPlus x.1 at h
  rw [x.2] at h
  exact h

theorem nativeChiralDiracPlusArrow_comp_minusArrow_apply
    (x : nativeMinusSector) :
    nativeChiralDiracPlusArrow (nativeChiralDiracMinusArrow x) =
      (3 : ℝ) • x := by
  apply Subtype.ext
  have h := congrArg
    (fun T : RealCl55FiniteModuleEndBridge.NativeSpinorCLM => T x.1)
    nativeChiralLaplacianMinus_eq_three_projector
  change nativeChiralDiracPlus (nativeChiralDiracMinus x.1) =
    (3 : ℝ) • nativeChiralProjectorMinus x.1 at h
  rw [x.2] at h
  exact h

noncomputable def plusArrowCLM :
    nativePlusSector →L[ℝ] nativeMinusSector :=
  LinearMap.toContinuousLinearMap nativeChiralDiracPlusArrow

noncomputable def minusArrowCLM :
    nativeMinusSector →L[ℝ] nativePlusSector :=
  LinearMap.toContinuousLinearMap nativeChiralDiracMinusArrow

theorem nativeChiralDiracPlusArrow_hilbert_adjoint :
    ContinuousLinearMap.adjoint plusArrowCLM = minusArrowCLM := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_right ℝ
  intro x
  have hA :=
    ContinuousLinearMap.adjoint_inner_left plusArrowCLM x y
  have hfull :=
    ContinuousLinearMap.adjoint_inner_left
      nativeChiralDiracPlus x.1 y.1
  rw [nativeChiralDiracPlus_hilbert_adjoint] at hfull
  exact hA.trans hfull.symm

theorem nativeChiralDiracPlusArrow_inner_smul
    (x y : nativePlusSector) :
    inner ℝ (nativeChiralDiracPlusArrow x).1
      (nativeChiralDiracPlusArrow y).1 =
      (3 : ℝ) * inner ℝ x.1 y.1 := by
  change inner ℝ (nativeChiralDiracPlus x.1)
      (nativeChiralDiracPlus y.1) =
    (3 : ℝ) * inner ℝ x.1 y.1
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [nativeChiralDiracPlus_hilbert_adjoint]
  change inner ℝ x.1
      (nativeChiralDiracMinus (nativeChiralDiracPlus y.1)) =
    (3 : ℝ) * inner ℝ x.1 y.1
  have h := congrArg Subtype.val
    (nativeChiralDiracMinusArrow_comp_plusArrow_apply y)
  change inner ℝ x.1
      (nativeChiralDiracMinusArrow (nativeChiralDiracPlusArrow y)).1 =
    (3 : ℝ) * inner ℝ x.1 y.1
  rw [h]
  change inner ℝ x.1 ((3 : ℝ) • y.1) = _
  rw [real_inner_smul_right]

theorem nativeChiralDiracMinusArrow_hilbert_adjoint :
    ContinuousLinearMap.adjoint minusArrowCLM = plusArrowCLM := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_right ℝ
  intro x
  have hA :=
    ContinuousLinearMap.adjoint_inner_left minusArrowCLM x y
  have hfull :=
    ContinuousLinearMap.adjoint_inner_left
      nativeChiralDiracMinus x.1 y.1
  rw [nativeChiralDiracMinus_hilbert_adjoint] at hfull
  exact hA.trans hfull.symm

theorem nativeChiralDiracMinusArrow_inner_smul
    (x y : nativeMinusSector) :
    inner ℝ (nativeChiralDiracMinusArrow x).1
      (nativeChiralDiracMinusArrow y).1 =
      (3 : ℝ) * inner ℝ x.1 y.1 := by
  change inner ℝ (nativeChiralDiracMinus x.1)
      (nativeChiralDiracMinus y.1) =
    (3 : ℝ) * inner ℝ x.1 y.1
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [nativeChiralDiracMinus_hilbert_adjoint]
  change inner ℝ x.1
      (nativeChiralDiracPlus (nativeChiralDiracMinus y.1)) =
    (3 : ℝ) * inner ℝ x.1 y.1
  have h := congrArg Subtype.val
    (nativeChiralDiracPlusArrow_comp_minusArrow_apply y)
  change inner ℝ x.1
      (nativeChiralDiracPlusArrow (nativeChiralDiracMinusArrow y)).1 =
    (3 : ℝ) * inner ℝ x.1 y.1
  rw [h]
  change inner ℝ x.1 ((3 : ℝ) • y.1) = _
  rw [real_inner_smul_right]

noncomputable def normalizedPlusArrow :
    nativePlusSector →ₗ[ℝ] nativeMinusSector :=
  (1 / Real.sqrt 3 : ℝ) • nativeChiralDiracPlusArrow

theorem normalizedPlusArrow_norm (x : nativePlusSector) :
    ‖normalizedPlusArrow x‖ = ‖x‖ := by
  have hinner : inner ℝ (normalizedPlusArrow x)
      (normalizedPlusArrow x) = inner ℝ x x := by
    change inner ℝ ((1 / Real.sqrt 3 : ℝ) •
        (nativeChiralDiracPlusArrow x).1)
      ((1 / Real.sqrt 3 : ℝ) •
        (nativeChiralDiracPlusArrow x).1) = _
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [nativeChiralDiracPlusArrow_inner_smul]
    have h3 : (Real.sqrt 3 : ℝ) * (Real.sqrt 3 : ℝ) = 3 :=
      Real.mul_self_sqrt (by norm_num)
    have hs : (1 / Real.sqrt 3 : ℝ) *
        (1 / Real.sqrt 3 : ℝ) * 3 = 1 := by
      calc
        (1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3 : ℝ) * 3 =
            (1 / (Real.sqrt 3 * Real.sqrt 3)) * 3 := by ring
        _ = (1 / 3) * 3 := by rw [h3]
        _ = 1 := by norm_num
    calc
      (1 / Real.sqrt 3 : ℝ) * ((1 / Real.sqrt 3) *
          (3 * inner ℝ x.1 x.1)) =
          ((1 / Real.sqrt 3 : ℝ) * (1 / Real.sqrt 3) * 3) *
            inner ℝ x.1 x.1 := by ring
      _ = inner ℝ x.1 x.1 := by rw [hs, one_mul]
  have hsq : ‖normalizedPlusArrow x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact hinner
  nlinarith [norm_nonneg (normalizedPlusArrow x), norm_nonneg x]

noncomputable def normalizedPlusArrowIsometry :
    nativePlusSector →ₗᵢ[ℝ] nativeMinusSector :=
  LinearIsometry.mk normalizedPlusArrow normalizedPlusArrow_norm

noncomputable def nativeChiralDiracPlusInverseArrow :
    nativeMinusSector →ₗ[ℝ] nativePlusSector where
  toFun x :=
    ⟨(1 / 3 : ℝ) • (nativeChiralDiracMinusArrow x).1, by
      change nativeChiralProjectorPlus
          ((1 / 3 : ℝ) • (nativeChiralDiracMinusArrow x).1) = _
      rw [map_smul, (nativeChiralDiracMinusArrow x).2]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul, smul_smul, mul_comm]

noncomputable def nativeChiralDiracMinusInverseArrow :
    nativePlusSector →ₗ[ℝ] nativeMinusSector where
  toFun x :=
    ⟨(1 / 3 : ℝ) • (nativeChiralDiracPlusArrow x).1, by
      change nativeChiralProjectorMinus
          ((1 / 3 : ℝ) • (nativeChiralDiracPlusArrow x).1) = _
      rw [map_smul, (nativeChiralDiracPlusArrow x).2]⟩
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c x := by
    apply Subtype.ext
    simp [map_smul, smul_smul, mul_comm]

theorem nativeChiralDiracPlusInverseArrow_left_inverse
  (x : nativePlusSector) :
    nativeChiralDiracPlusInverseArrow (nativeChiralDiracPlusArrow x) = x := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (nativeChiralDiracMinusArrow_comp_plusArrow_apply x)
  have h' : nativeChiralDiracMinus
      (nativeChiralDiracPlus x.1) = (3 : ℝ) • x.1 := by
    simpa using h
  change (1 / 3 : ℝ) •
      nativeChiralDiracMinus (nativeChiralDiracPlus x.1) = x.1
  rw [h']
  rw [smul_smul]
  norm_num

theorem nativeChiralDiracMinusInverseArrow_left_inverse
  (x : nativeMinusSector) :
    nativeChiralDiracMinusInverseArrow (nativeChiralDiracMinusArrow x) = x := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (nativeChiralDiracPlusArrow_comp_minusArrow_apply x)
  have h' : nativeChiralDiracPlus
      (nativeChiralDiracMinus x.1) = (3 : ℝ) • x.1 := by
    simpa using h
  change (1 / 3 : ℝ) •
      nativeChiralDiracPlus (nativeChiralDiracMinus x.1) = x.1
  rw [h']
  rw [smul_smul]
  norm_num

theorem nativeChiralDiracPlusArrow_comp_plusInverseArrow
  (x : nativeMinusSector) :
    nativeChiralDiracPlusArrow
        (nativeChiralDiracPlusInverseArrow x) = x := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (nativeChiralDiracPlusArrow_comp_minusArrow_apply x)
  have h' : nativeChiralDiracPlus
      (nativeChiralDiracMinus x.1) = (3 : ℝ) • x.1 := by
    simpa using h
  have h'' : nativeChiralDiracPlus
      (nativeChiralDiracMinusArrow x).1 = (3 : ℝ) • x.1 := by
    simpa [nativeChiralDiracMinusArrow] using h'
  change nativeChiralDiracPlus
      ((1 / 3 : ℝ) • (nativeChiralDiracMinusArrow x).1) = x.1
  rw [map_smul]
  rw [h'']
  module

theorem nativeChiralDiracMinusArrow_comp_minusInverseArrow
  (x : nativePlusSector) :
    nativeChiralDiracMinusArrow
        (nativeChiralDiracMinusInverseArrow x) = x := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (nativeChiralDiracMinusArrow_comp_plusArrow_apply x)
  have h' : nativeChiralDiracMinus
      (nativeChiralDiracPlus x.1) = (3 : ℝ) • x.1 := by
    simpa using h
  have h'' : nativeChiralDiracMinus
      (nativeChiralDiracPlusArrow x).1 = (3 : ℝ) • x.1 := by
    simpa [nativeChiralDiracPlusArrow] using h'
  change nativeChiralDiracMinus
      ((1 / 3 : ℝ) • (nativeChiralDiracPlusArrow x).1) = x.1
  rw [map_smul]
  rw [h'']
  module

theorem nativeChiralDiracPlusArrow_bijective :
    Function.Bijective nativeChiralDiracPlusArrow := by
  constructor
  · intro x y hxy
    calc
      x = nativeChiralDiracPlusInverseArrow
          (nativeChiralDiracPlusArrow x) :=
        (nativeChiralDiracPlusInverseArrow_left_inverse x).symm
      _ = nativeChiralDiracPlusInverseArrow
          (nativeChiralDiracPlusArrow y) := by rw [hxy]
      _ = y := nativeChiralDiracPlusInverseArrow_left_inverse y
  · intro y
    exact ⟨nativeChiralDiracPlusInverseArrow y,
      nativeChiralDiracPlusArrow_comp_plusInverseArrow y⟩

theorem nativeChiralDiracMinusArrow_bijective :
    Function.Bijective nativeChiralDiracMinusArrow := by
  constructor
  · intro x y hxy
    calc
      x = nativeChiralDiracMinusInverseArrow
          (nativeChiralDiracMinusArrow x) :=
        (nativeChiralDiracMinusInverseArrow_left_inverse x).symm
      _ = nativeChiralDiracMinusInverseArrow
          (nativeChiralDiracMinusArrow y) := by rw [hxy]
      _ = y := nativeChiralDiracMinusInverseArrow_left_inverse y
  · intro y
    exact ⟨nativeChiralDiracMinusInverseArrow y,
      nativeChiralDiracMinusArrow_comp_minusInverseArrow y⟩

noncomputable def nativeChiralDiracPlusEquiv :
    nativePlusSector ≃ₗ[ℝ] nativeMinusSector :=
  LinearEquiv.ofBijective nativeChiralDiracPlusArrow
    nativeChiralDiracPlusArrow_bijective

noncomputable def nativeChiralDiracMinusEquiv :
    nativeMinusSector ≃ₗ[ℝ] nativePlusSector :=
  LinearEquiv.ofBijective nativeChiralDiracMinusArrow
    nativeChiralDiracMinusArrow_bijective

@[simp] theorem nativeChiralDiracPlusEquiv_apply
    (x : nativePlusSector) :
    nativeChiralDiracPlusEquiv x = nativeChiralDiracPlusArrow x := rfl

@[simp] theorem nativeChiralDiracMinusEquiv_apply
    (x : nativeMinusSector) :
    nativeChiralDiracMinusEquiv x = nativeChiralDiracMinusArrow x := rfl

theorem nativePlusSectorAction_intertwines_chiralDiracPlusInverse
    (act : G2IntegratedAction G) (g : G) :
    (nativePlusSectorAction act g).comp
        nativeChiralDiracPlusInverseArrow =
      nativeChiralDiracPlusInverseArrow.comp
        (nativeMinusSectorAction act g) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change nativeIntegratedAction act g
      ((1 / 3 : ℝ) • (nativeChiralDiracMinusArrow x).1) =
    (1 / 3 : ℝ) • nativeChiralDiracMinusArrow
      (nativeMinusSectorAction act g x)
  rw [map_smul]
  have h := congrArg
    (fun T : nativeMinusSector →ₗ[ℝ] nativePlusSector => T x)
    (nativeMinusSectorAction_intertwines_chiralDiracMinus act g)
  have h := congrArg Subtype.val h
  have h' : nativeIntegratedAction act g
      (nativeChiralDiracMinusArrow x).1 =
      nativeChiralDiracMinusArrow
        (nativeMinusSectorAction act g x) := by
    simpa [ContinuousLinearMap.comp_apply] using h
  rw [h']

theorem nativeMinusSectorAction_intertwines_chiralDiracMinusInverse
    (act : G2IntegratedAction G) (g : G) :
    (nativeMinusSectorAction act g).comp
        nativeChiralDiracMinusInverseArrow =
      nativeChiralDiracMinusInverseArrow.comp
        (nativePlusSectorAction act g) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change nativeIntegratedAction act g
      ((1 / 3 : ℝ) • (nativeChiralDiracPlusArrow x).1) =
    (1 / 3 : ℝ) • nativeChiralDiracPlusArrow
      (nativePlusSectorAction act g x)
  rw [map_smul]
  have h := congrArg
    (fun T : nativePlusSector →ₗ[ℝ] nativeMinusSector => T x)
    (nativePlusSectorAction_intertwines_chiralDiracPlus act g)
  have h := congrArg Subtype.val h
  have h' : nativeIntegratedAction act g
      (nativeChiralDiracPlusArrow x).1 =
      nativeChiralDiracPlusArrow
        (nativePlusSectorAction act g x) := by
    simpa [ContinuousLinearMap.comp_apply] using h
  rw [h']

theorem nativeChiralDiracPlusArrow_kernel_trivial :
    LinearMap.ker nativeChiralDiracPlusArrow = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  exact nativeChiralDiracPlusArrow_bijective.1 hxy

theorem nativeChiralDiracMinusArrow_kernel_trivial :
    LinearMap.ker nativeChiralDiracMinusArrow = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  exact nativeChiralDiracMinusArrow_bijective.1 hxy

/-! The finite chiral arrows have equal dimensions and hence zero algebraic
index.  The statement is expressed by explicit bijectivity, avoiding any
claim that a completed Fredholm or Kasparov index has been constructed. -/
theorem nativeChiralHodge_finite_index_zero :
    Function.Bijective nativeChiralDiracPlusArrow ∧
      Function.Bijective nativeChiralDiracMinusArrow := by
  exact ⟨nativeChiralDiracPlusArrow_bijective,
    nativeChiralDiracMinusArrow_bijective⟩

end InfoGeometry.Canonical.RealCl55NativeChiralHodgeIndexBridge
