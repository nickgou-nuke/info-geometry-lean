import InfoGeometry.Lie.SplitOctonionImaginaryEllSupport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionImaginaryCircularForm
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
import InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
import InfoGeometry.Canonical.ZornCliffordRepresentation

/-!
# Native range reduction for the imaginary ell support

The intrinsic active support is defined as `range (T²)`.  This owner records
only the native reduction to `range T`, using the already proved tripotence
of the restricted operator.  The subsequent dimension theorem is deliberately
left for a separate basis/rank-nullity owner.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionImaginaryEllSupportDimension

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionImaginaryEllPolarization
open InfoGeometry.Lie.SplitOctonionImaginaryEllSupport
open InfoGeometry.Lie.SplitOctonionImaginaryCircularForm
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Algebra.Zorn.SplitOctonionWittPlanes
open InfoGeometry.Canonical.ZornClifford

abbrev Imaginary := SplitOctonionImaginaryAction.Imaginary
abbrev Support := SplitOctonionImaginaryEllSupport.Support

private def activeIndex : Fin 3 ⊕ Fin 3 → Fin 8
  | Sum.inl i => ⟨i.1 + 1, by omega⟩
  | Sum.inr i => ⟨i.1 + 5, by omega⟩

private def activeCartesian : Fin 3 ⊕ Fin 3 → CartesianCoordinates
  | Sum.inl i => rootPlus i
  | Sum.inr i => rootMinus i

private theorem activeIndex_injective : Function.Injective activeIndex := by
  intro i j h
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          apply congrArg Sum.inl
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp [activeIndex] at hv
          exact hv
      | inr j => have := congrArg Fin.val h; simp [activeIndex] at this; omega
  | inr i =>
      cases j with
      | inl j => have := congrArg Fin.val h; simp [activeIndex] at this; omega
      | inr j =>
          apply congrArg Sum.inr
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp [activeIndex] at hv
          omega

private theorem activeCartesian_linearIndependent :
    LinearIndependent ℝ activeCartesian := by
  have hEq : activeCartesian = circularFrame ∘ activeIndex := by
    funext i
    cases i with
    | inl j => fin_cases j <;> rfl
    | inr j => fin_cases j <;> rfl
  rw [hEq]
  exact circularFrame_linearIndependent.comp activeIndex activeIndex_injective

theorem activeCircularDirections_linearIndependent :
    LinearIndependent ℝ (fun i : Fin 3 ⊕ Fin 3 =>
      match i with
      | Sum.inl j => upperAxis j
      | Sum.inr j => lowerAxis j) := by
  apply LinearIndependent.of_comp (Submodule.subtype Imaginary)
  have h := activeCartesian_linearIndependent
  have hmap := h.map' cartesianZornLinearEquiv.toLinearMap (by
    rw [LinearMap.ker_eq_bot]
    exact cartesianZornLinearEquiv.injective)
  have hEq : (Submodule.subtype Imaginary ∘ (fun i : Fin 3 ⊕ Fin 3 =>
      match i with
      | Sum.inl j => upperAxis j
      | Sum.inr j => lowerAxis j)) =
      cartesianZornLinearEquiv.toLinearMap ∘ activeCartesian := by
    funext i
    cases i <;> rfl
  rw [hEq]
  exact hmap

theorem finrank_activeCircularSpan :
    Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun i : Fin 3 ⊕ Fin 3 =>
          match i with
          | Sum.inl j => upperAxis j
          | Sum.inr j => lowerAxis j))) = 6 := by
  rw [finrank_span_eq_card activeCircularDirections_linearIndependent]
  simp


private theorem imaginaryEllT_range_sq_eq_range :
    LinearMap.range (imaginaryEllT * imaginaryEllT) =
      LinearMap.range imaginaryEllT := by
  apply le_antisymm
  · rintro X ⟨Y, rfl⟩
    exact ⟨imaginaryEllT Y, rfl⟩
  · rintro X ⟨Y, rfl⟩
    refine ⟨imaginaryEllT Y, ?_⟩
    have h := congrArg (fun F : Module.End ℝ Imaginary => F Y)
      imaginaryEllT_tripotent
    simpa [pow_three, Module.End.mul_apply] using h

theorem activeSupport_eq_range_imaginaryEllT :
    Support = LinearMap.range imaginaryEllT := by
  exact imaginaryEllT_range_sq_eq_range

theorem imaginaryEllT_a (X : Imaginary) :
    (imaginaryEllT X).1.a = (X.1.y 0 - X.1.x 0) / 2 := by
  simp [imaginaryEllT, imaginaryEllCommutator,
    InfoGeometry.Lie.SplitOctonionEllPolarization.ellCommutator,
    lUnit, InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
    Fin.sum_univ_three]
  ring

theorem imaginaryEllT_b (X : Imaginary) :
    (imaginaryEllT X).1.b = (X.1.x 0 - X.1.y 0) / 2 := by
  simp [imaginaryEllT, imaginaryEllCommutator,
    InfoGeometry.Lie.SplitOctonionEllPolarization.ellCommutator,
    lUnit, InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
    InfoGeometry.Canonical.ZornMatrix.dot,
    Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
    Fin.sum_univ_three]
  ring

theorem imaginaryEllT_x (X : Imaginary) :
    (imaginaryEllT X).1.x =
      ((X.1.b - X.1.a) / 2) • (Pi.single 0 1 : Fin 3 → ℝ) -
        InfoGeometry.Canonical.ZornMatrix.cross (Pi.single 0 1) X.1.y := by
  funext i
  fin_cases i <;>
    simp [imaginaryEllT, imaginaryEllCommutator,
      InfoGeometry.Lie.SplitOctonionEllPolarization.ellCommutator,
      lUnit, InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      Fin.sum_univ_three, Pi.single_apply]
  <;> ring

theorem imaginaryEllT_y (X : Imaginary) :
    (imaginaryEllT X).1.y =
      ((X.1.a - X.1.b) / 2) • (Pi.single 0 1 : Fin 3 → ℝ) +
        InfoGeometry.Canonical.ZornMatrix.cross (Pi.single 0 1) X.1.x := by
  funext i
  fin_cases i <;>
    simp [imaginaryEllT, imaginaryEllCommutator,
      InfoGeometry.Lie.SplitOctonionEllPolarization.ellCommutator,
      lUnit, InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      Fin.sum_univ_three, Pi.single_apply]
  <;> ring

theorem imaginaryEllT_kernel_eq_span :
    LinearMap.ker imaginaryEllT =
      ℝ ∙ InfoGeometry.Lie.SplitOctonionEllPolarization.ellImaginary := by
  apply le_antisymm
  · intro X hX
    have hzero : imaginaryEllT X = 0 := LinearMap.mem_ker.mp hX
    have ha := congrArg (fun Z : Imaginary => Z.1.a) hzero
    change (imaginaryEllT X).1.a = 0 at ha
    rw [imaginaryEllT_a] at ha
    have hb := congrArg (fun Z : Imaginary => Z.1.b) hzero
    change (imaginaryEllT X).1.b = 0 at hb
    rw [imaginaryEllT_b] at hb
    have hx := congrArg (fun Z : Imaginary => Z.1.x) hzero
    change (imaginaryEllT X).1.x = 0 at hx
    rw [imaginaryEllT_x] at hx
    have hy := congrArg (fun Z : Imaginary => Z.1.y) hzero
    change (imaginaryEllT X).1.y = 0 at hy
    rw [imaginaryEllT_y] at hy
    have htrace := X.2
    change X.1.a + X.1.b = 0 at htrace
    have hba : X.1.b - X.1.a = 0 := by
      have h := congrFun hx 0
      simp [InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at h
      linarith
    have ha0 : X.1.a = 0 := by linarith
    have hb0 : X.1.b = 0 := by linarith
    have hy20 : X.1.y 2 = 0 := by
      have h := congrFun hx 1
      simp [InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at h
      linarith
    have hy10 : X.1.y 1 = 0 := by
      have h := congrFun hx 2
      simp [InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at h
      linarith
    have hx20 : X.1.x 2 = 0 := by
      have h := congrFun hy 1
      simp [InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at h
      linarith
    have hx10 : X.1.x 1 = 0 := by
      have h := congrFun hy 2
      simp [InfoGeometry.Canonical.ZornMatrix.cross, Pi.single_apply] at h
      linarith
    have hy0 : X.1.y 0 = X.1.x 0 := by linarith
    rw [Submodule.mem_span_singleton]
    refine ⟨X.1.x 0, ?_⟩
    apply imaginaryCoordLinearEquiv.injective
    apply Prod.ext
    · simp [imaginaryCoordLinearEquiv,
        InfoGeometry.Lie.SplitOctonionEllPolarization.ellImaginary,
        lUnit,
        Pi.single_apply, smul_a, smul_b, smul_x, smul_y,
        ha0, hb0, hy0]
    · apply Prod.ext <;>
        funext i <;> fin_cases i <;>
        simp [imaginaryCoordLinearEquiv,
          InfoGeometry.Lie.SplitOctonionEllPolarization.ellImaginary,
          lUnit,
          Pi.single_apply, smul_a, smul_b, smul_x, smul_y,
          hx10, hx20, hy0, hy10, hy20]
  · apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    simp [imaginaryEllT, imaginaryEllCommutator,
      InfoGeometry.Lie.SplitOctonionEllPolarization.ellCommutator,
      InfoGeometry.Lie.SplitOctonionEllPolarization.ellImaginary,
      lUnit, InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv]

theorem finrank_activeSupport : Module.finrank ℝ Support = 6 := by
  rw [activeSupport_eq_range_imaginaryEllT]
  letI : FiniteDimensional ℝ Imaginary :=
    LinearEquiv.finiteDimensional imaginaryCoordLinearEquiv.symm
  have hne :
      InfoGeometry.Lie.SplitOctonionEllPolarization.ellImaginary ≠ 0 := by
    intro h
    have hx := congrArg (fun Z : Imaginary => Z.1.x 0) h
    simp [InfoGeometry.Lie.SplitOctonionEllPolarization.ellImaginary,
      lUnit] at hx
  have hrank := LinearMap.finrank_range_add_finrank_ker imaginaryEllT
  rw [imaginaryEllT_kernel_eq_span, finrank_span_singleton hne,
    finrank_imaginary] at hrank
  apply Nat.add_right_cancel (m := 1)
  calc
    Module.finrank ℝ (LinearMap.range imaginaryEllT) + 1 = 7 := hrank
    _ = 6 + 1 := by norm_num

/-! ## Intrinsic `1 + 6` carrier decomposition -/

theorem imaginaryEllT_axis_sup_support_eq_top :
    (ℝ ∙ InfoGeometry.Lie.SplitOctonionEllPolarization.ellImaginary) ⊔
        Support = ⊤ := by
  rw [← imaginaryEllT_kernel_eq_span]
  exact imaginaryEllT_kernel_support_sup_eq_top

theorem imaginaryEllT_axis_inf_support_eq_bot :
    (ℝ ∙ InfoGeometry.Lie.SplitOctonionEllPolarization.ellImaginary) ⊓
        Support = ⊥ := by
  rw [← imaginaryEllT_kernel_eq_span]
  exact imaginaryEllT_kernel_support_inf_eq_bot

end InfoGeometry.Lie.SplitOctonionImaginaryEllSupportDimension
