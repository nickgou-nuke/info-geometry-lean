import Mathlib
import InfoGeometry.Canonical.SplitSpinFactorTKKSO66

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinFactorTKKInjectivity

open InfoGeometry.Canonical.SplitSpinFactorTKKSO66
open InfoGeometry.Canonical.SplitOctonionTKKFiniteDimensionalBridges

abbrev V10 := SplitSpinFactorTKKSO66.V10
abbrev Carrier12 := SplitSpinFactorTKKSO66.Carrier12
abbrev End12 := SplitSpinFactorTKKSO66.End12

@[simp] theorem B10_zero_right (u : V10) : B10 u 0 = 0 := by
  simpa using (B10_smul_right (0 : ℝ) u (0 : V10))

@[simp] theorem B10_zero_left (v : V10) : B10 0 v = 0 := by
  rw [B10_symm, B10_zero_right]

/-- Intrinsic middle-grade carrier: all endomorphisms skew for the polarized
split `(5,5)` form. -/
def B10SkewEnd : Submodule ℝ (Module.End ℝ V10) where
  carrier := {A | ∀ u v, B10 (A u) v + B10 u (A v) = 0}
  zero_mem' := by
    intro u v
    simp
  add_mem' := by
    intro A C hA hC u v
    simp only [LinearMap.add_apply, B10_add_left, B10_add_right]
    linarith [hA u v, hC u v]
  smul_mem' := by
    intro r A hA u v
    simp only [LinearMap.smul_apply, B10_smul_left, B10_smul_right]
    rw [← mul_add, hA u v, mul_zero]

/-- Test-vector separation of all four TKK parameter blocks.  No dimension or
skewness assumption on the middle endomorphism is needed. -/
theorem tkk_param_zero_components
    (u : V10) (lambda : ℝ) (A : Module.End ℝ V10) (v : V10)
    (hzero : translation u + dilation lambda + middleRotation A +
      specialConformal v = 0) :
    u = 0 ∧ lambda = 0 ∧ A = 0 ∧ v = 0 := by
  have h1 :
      (translation u + dilation lambda + middleRotation A + specialConformal v)
          ((1 : ℝ), ((0 : V10), (0 : ℝ))) = 0 := by
    rw [hzero]
    rfl
  have hlambda : lambda = 0 := by
    have h := congrArg (fun p : Carrier12 => p.1) h1
    simpa [translation, dilation, middleRotation, specialConformal] using h
  have hv : v = 0 := by
    have h := congrArg (fun p : Carrier12 => p.2.1) h1
    simpa [translation, dilation, middleRotation, specialConformal] using h
  have h2 :
      (translation u + dilation lambda + middleRotation A + specialConformal v)
          ((0 : ℝ), ((0 : V10), (1 : ℝ))) = 0 := by
    rw [hzero]
    rfl
  have hu : u = 0 := by
    have h := congrArg (fun p : Carrier12 => p.2.1) h2
    simpa [translation, dilation, middleRotation, specialConformal] using h
  have hA : A = 0 := by
    apply LinearMap.ext
    intro z
    have hz :
        (translation u + dilation lambda + middleRotation A + specialConformal v)
            ((0 : ℝ), (z, (0 : ℝ))) = 0 := by
      rw [hzero]
      rfl
    have h := congrArg (fun p : Carrier12 => p.2.1) hz
    rw [hu, hlambda, hv] at h
    simpa [translation, dilation, middleRotation, specialConformal] using h
  exact ⟨hu, hlambda, hA, hv⟩

/-- Parameter carrier for the concrete three grading:
`g_-1 ⊕ (R D ⊕ so(B10)) ⊕ g_+1`. -/
abbrev TKKParam := V10 × ((ℝ × B10SkewEnd) × V10)

/-- Linear parameterization of the three-graded conformal generators. -/
def tkkParamMap : TKKParam →ₗ[ℝ] End12 where
  toFun p :=
    translation p.1 + dilation p.2.1.1 +
      middleRotation p.2.1.2.1 + specialConformal p.2.2
  map_add' p q := by
    apply LinearMap.ext
    intro x
    ext <;>
      simp [translation, dilation, middleRotation, specialConformal,
        B10_add_left, B10_add_right] <;> ring
  map_smul' r p := by
    apply LinearMap.ext
    intro x
    ext <;>
      simp [translation, dilation, middleRotation, specialConformal,
        B10_smul_left, B10_smul_right, smul_smul] <;> ring

/-- The full TKK parameterization is injective by the three test-vector
readouts. -/
theorem tkkParamMap_injective : Function.Injective tkkParamMap := by
  rw [LinearMap.injective_iff_map_eq_zero]
  rintro ⟨u, ⟨⟨lambda, A⟩, v⟩⟩ hzero
  change translation u + dilation lambda + middleRotation A.1 +
      specialConformal v = 0 at hzero
  rcases tkk_param_zero_components u lambda A.1 v hzero with
    ⟨hu, hlambda, hA, hv⟩
  have hAsub : A = 0 := Subtype.ext hA
  subst u
  subst lambda
  subst A
  subst v
  rfl

/-- Every parameterized generator is infinitesimally skew for `B66`. -/
theorem tkkParamMap_isB66Skew (p : TKKParam) :
    IsB66Skew (tkkParamMap p) := by
  intro x y
  rcases p with ⟨u, ⟨⟨lambda, A⟩, v⟩⟩
  change
    B66 ((translation u + dilation lambda + middleRotation A.1 +
      specialConformal v) x) y +
    B66 x ((translation u + dilation lambda + middleRotation A.1 +
      specialConformal v) y) = 0
  have ht := translation_isB66Skew u x y
  have hd := dilation_isB66Skew lambda x y
  have hm := middleRotation_isB66Skew A.1 A.2 x y
  have hk := specialConformal_isB66Skew v x y
  simp only [LinearMap.add_apply]
  simp [B66, B10_add_left, B10_add_right] at ht hd hm hk ⊢
  linarith

/-- The parameter carrier is linearly equivalent to the range of the concrete
TKK action. -/
noncomputable def tkkParamRangeEquiv :
    TKKParam ≃ₗ[ℝ] LinearMap.range tkkParamMap :=
  LinearEquiv.ofInjective tkkParamMap tkkParamMap_injective

/-- If the intrinsic `B10`-skew middle carrier has the expected finrank 45,
the complete parameter space has finrank 66. -/
theorem tkkParam_finrank_of_skew_finrank
    (h45 : Module.finrank ℝ B10SkewEnd = 45) :
    Module.finrank ℝ TKKParam = 66 := by
  have h10 : Module.finrank ℝ V10 = 10 := tkk_dimension_packet.1
  simp [TKKParam, Module.finrank_prod, h10, h45]

/-- The same assumption yields a 66-dimensional realized subspace of
`End(V12)`. -/
theorem tkkParamRange_finrank_of_skew_finrank
    (h45 : Module.finrank ℝ B10SkewEnd = 45) :
    Module.finrank ℝ (LinearMap.range tkkParamMap) = 66 := by
  calc
    Module.finrank ℝ (LinearMap.range tkkParamMap) =
        Module.finrank ℝ TKKParam := tkkParamRangeEquiv.finrank_eq.symm
    _ = 66 := tkkParam_finrank_of_skew_finrank h45

/-- Soldering socket between the intrinsic spin-factor skew endomorphisms and
the repository's already certified 45-dimensional `So55` carrier. -/
structure SO55Soldering where
  equiv : B10SkewEnd ≃ₗ[ℝ] So55

/-- A soldering to native `So55` closes the 45-dimensional middle-grade gap. -/
theorem B10SkewEnd_finrank_of_soldering (S : SO55Soldering) :
    Module.finrank ℝ B10SkewEnd = 45 := by
  calc
    Module.finrank ℝ B10SkewEnd = Module.finrank ℝ So55 := S.equiv.finrank_eq
    _ = 45 := so55_finrank

/-- With only a carrier soldering to the certified `So55`, the concrete TKK
range is already forced to have dimension 66. -/
theorem tkkParamRange_finrank_of_soldering (S : SO55Soldering) :
    Module.finrank ℝ (LinearMap.range tkkParamMap) = 66 :=
  tkkParamRange_finrank_of_skew_finrank
    (B10SkewEnd_finrank_of_soldering S)

end InfoGeometry.Canonical.SplitSpinFactorTKKInjectivity
