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
