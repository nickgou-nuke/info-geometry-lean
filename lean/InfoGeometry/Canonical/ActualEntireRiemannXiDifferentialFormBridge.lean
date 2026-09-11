import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiRegularLogDerivativeBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
import InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeSchwarzBridge

/-!
# Native differential-form readout for the entire Riemann `xi`

The existing actual logarithmic readout is a continuous linear one-form at
each point.  This owner packages it as a genuine Mathlib degree-one
differential form on `ℂ`.  The form is defined using totalized division at
zeros; unconditional closedness, a contour period, and a de Rham cohomology
class are not asserted.  A conditional one-dimensional `extDeriv` theorem is
included for downstream domains with the required differentiability data.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiDifferentialFormBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiRegularLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeSchwarzBridge

/-! ## One-dimensional scalar one-form closedness -/

noncomputable def scalarComplexOneFormLinearMap :
    (ℂ →L[ℂ] ℂ) →ₗ[ℂ] ℂ [⋀^Fin 1]→L[ℂ] ℂ :=
  { toFun := ContinuousAlternatingMap.ofSubsingleton ℂ ℂ ℂ (0 : Fin 1)
    map_add' := by
      intro x y
      apply ContinuousAlternatingMap.ext
      intro v
      simp
    map_smul' := by
      intro c x
      apply ContinuousAlternatingMap.ext
      intro v
      simp }

noncomputable def scalarComplexOneFormContinuousLinearMap :
    (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ [⋀^Fin 1]→L[ℂ] ℂ :=
  { toLinearMap := scalarComplexOneFormLinearMap
    cont := LinearMap.continuous_of_finiteDimensional
      scalarComplexOneFormLinearMap }

/-- The explicit scalar one-form associated to a complex coefficient. -/
noncomputable def scalarComplexOneForm (a : ℂ → ℂ) :
    ℂ → ℂ [⋀^Fin 1]→L[ℂ] ℂ :=
  fun s => scalarComplexOneFormContinuousLinearMap
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (a s))

@[simp] theorem scalarComplexOneForm_apply (a : ℂ → ℂ) (s : ℂ)
    (v : Fin 1 → ℂ) : scalarComplexOneForm a s v = v 0 * a s := by
  simp [scalarComplexOneForm, scalarComplexOneFormContinuousLinearMap,
    scalarComplexOneFormLinearMap]

/--
On the one-dimensional complex carrier, the exterior derivative of an
explicit scalar one-form vanishes whenever both the coefficient and the
form have the differentiability required by `extDeriv_apply`.
-/
theorem scalarComplexOneForm_extDeriv_eq_zero
    (a : ℂ → ℂ) (s : ℂ)
    (ha : DifferentiableAt ℂ a s)
    (hform : DifferentiableAt ℂ (scalarComplexOneForm a) s) :
    extDeriv (scalarComplexOneForm a) s = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  rw [extDeriv_apply hform v]
  rw [Fin.sum_univ_two]
  rw [Fin.removeNth_zero]
  rw [show (1 : Fin 2) = Fin.last 1 by rfl, Fin.removeNth_last]
  have htail : Fin.tail v 0 = v 1 := by
    rfl
  have hinit : Fin.init v 0 = v 0 := by
    rfl
  have hfun_tail :
      (fun x => (scalarComplexOneForm a x) (Fin.tail v)) =
        (fun x => v 1 * a x) := by
    funext x
    rw [scalarComplexOneForm_apply]
    rfl
  have hfun_init :
      (fun x => (scalarComplexOneForm a x) (Fin.init v)) =
        (fun x => v 0 * a x) := by
    funext x
    rw [scalarComplexOneForm_apply]
    rfl
  rw [hfun_tail, hfun_init]
  rw [fderiv_const_mul ha, fderiv_const_mul ha]
  simp [smul_eq_mul]
  ring

theorem scalarComplexOneForm_differentiableAt
    (a : ℂ → ℂ) (s : ℂ)
    (ha : DifferentiableAt ℂ a s) :
    DifferentiableAt ℂ (scalarComplexOneForm a) s := by
  unfold scalarComplexOneForm
  have hsmul : DifferentiableAt ℂ
      (fun z : ℂ => (a z) • (1 : ℂ →L[ℂ] ℂ)) s :=
    ha.smul (differentiableAt_const (c := (1 : ℂ →L[ℂ] ℂ)))
  have heq : (fun z : ℂ => ContinuousLinearMap.smulRight
      (1 : ℂ →L[ℂ] ℂ) (a z)) =
      (fun z : ℂ => (a z) • (1 : ℂ →L[ℂ] ℂ)) := by
    funext z
    ext
    simp [ContinuousLinearMap.smulRight_apply]
  have hclm : DifferentiableAt ℂ (fun z : ℂ =>
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (a z)) s := by
    rw [heq]
    exact hsmul
  exact scalarComplexOneFormContinuousLinearMap.differentiableAt.comp s hclm

/-- The actual entire `xi` logarithmic coefficient as a native 1-form. -/
noncomputable def entireRiemannXiLogDifferentialForm :
    ℂ → ℂ [⋀^Fin 1]→L[ℂ] ℂ :=
  fun s =>
    ContinuousAlternatingMap.ofSubsingleton ℂ ℂ ℂ (0 : Fin 1)
      (entireRiemannXiLogOneForm s)

theorem entireRiemannXiLogDifferentialForm_eq_scalarComplexOneForm :
    entireRiemannXiLogDifferentialForm =
      scalarComplexOneForm entireRiemannXiLogDifferential := by
  funext z
  apply ContinuousAlternatingMap.ext
  intro v
  simp [entireRiemannXiLogDifferentialForm,
    scalarComplexOneForm, scalarComplexOneFormContinuousLinearMap,
    scalarComplexOneFormLinearMap, entireRiemannXiLogOneForm]

/--
The logarithmic coefficient is differentiable at a nonzero point whenever
the derivative of the entire xi representative is differentiable there.
This is the precise regularity input needed before applying the conditional
`extDeriv` theorem below; no second-derivative regularity is inferred here.
-/
theorem entireRiemannXiLogDifferential_differentiableAt
    (s : ℂ)
    (hderiv : DifferentiableAt ℂ (deriv entireRiemannXi) s)
    (hzero : entireRiemannXi s ≠ 0) :
    DifferentiableAt ℂ entireRiemannXiLogDifferential s := by
  unfold entireRiemannXiLogDifferential
  exact (hderiv.div (differentiable_entireRiemannXi.differentiableAt)
    hzero).neg

theorem entireRiemannXiLogDifferentialForm_differentiableAt
    (s : ℂ)
    (hderiv : DifferentiableAt ℂ (deriv entireRiemannXi) s)
    (hzero : entireRiemannXi s ≠ 0) :
    DifferentiableAt ℂ entireRiemannXiLogDifferentialForm s := by
  rw [entireRiemannXiLogDifferentialForm_eq_scalarComplexOneForm]
  exact scalarComplexOneForm_differentiableAt _ _
    (entireRiemannXiLogDifferential_differentiableAt s hderiv hzero)

theorem entireRiemannXiLogDifferential_differentiableOn_zero_free :
    DifferentiableOn ℂ entireRiemannXiLogDifferential
      entireRiemannXiZeroFreeLocus := by
  intro s hs
  have hs0 : entireRiemannXi s ≠ 0 :=
    (mem_entireRiemannXiZeroFreeLocus s).mp hs
  exact (entireRiemannXiLogDifferential_differentiableAt s
    (differentiable_deriv_entireRiemannXi.differentiableAt) hs0).differentiableWithinAt

theorem entireRiemannXiLogDifferentialForm_differentiableOn_zero_free :
    DifferentiableOn ℂ entireRiemannXiLogDifferentialForm
      entireRiemannXiZeroFreeLocus := by
  intro s hs
  have hs0 : entireRiemannXi s ≠ 0 :=
    (mem_entireRiemannXiZeroFreeLocus s).mp hs
  exact (entireRiemannXiLogDifferentialForm_differentiableAt s
    (differentiable_deriv_entireRiemannXi.differentiableAt) hs0).differentiableWithinAt

theorem entireRiemannXiLogDifferential_circleIntegrable_of_closedBall_subset_zero_free
    (rho : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hball : Metric.closedBall rho R ⊆ entireRiemannXiZeroFreeLocus) :
    CircleIntegrable entireRiemannXiLogDifferential rho R := by
  have hcont : ContinuousOn entireRiemannXiLogDifferential
      entireRiemannXiZeroFreeLocus :=
    entireRiemannXiLogDifferential_differentiableOn_zero_free.continuousOn
  have hsphere : Metric.sphere rho R ⊆ entireRiemannXiZeroFreeLocus := by
    intro z hz
    exact hball (Metric.sphere_subset_closedBall hz)
  exact (hcont.mono hsphere).circleIntegrable hR

theorem entireRiemannXiLogDifferentialForm_extDeriv_eq_zero
    (s : ℂ)
    (ha : DifferentiableAt ℂ entireRiemannXiLogDifferential s)
    (hform : DifferentiableAt ℂ entireRiemannXiLogDifferentialForm s) :
    extDeriv entireRiemannXiLogDifferentialForm s = 0 := by
  rw [entireRiemannXiLogDifferentialForm_eq_scalarComplexOneForm]
  exact scalarComplexOneForm_extDeriv_eq_zero
    entireRiemannXiLogDifferential s ha (by simpa using hform)

theorem entireRiemannXiLogDifferentialForm_extDeriv_eq_zero_of_differentiableAt_deriv
    (s : ℂ)
    (hderiv : DifferentiableAt ℂ (deriv entireRiemannXi) s)
    (hzero : entireRiemannXi s ≠ 0) :
    extDeriv entireRiemannXiLogDifferentialForm s = 0 := by
  exact entireRiemannXiLogDifferentialForm_extDeriv_eq_zero s
    (entireRiemannXiLogDifferential_differentiableAt s hderiv hzero)
    (entireRiemannXiLogDifferentialForm_differentiableAt s hderiv hzero)

theorem entireRiemannXiLogDifferentialForm_extDeriv_eq_zero_actual
    (s : ℂ) (hzero : entireRiemannXi s ≠ 0) :
    extDeriv entireRiemannXiLogDifferentialForm s = 0 := by
  exact entireRiemannXiLogDifferentialForm_extDeriv_eq_zero_of_differentiableAt_deriv
    s (differentiable_deriv_entireRiemannXi).differentiableAt hzero

theorem entireRiemannXiLogDifferentialFormOnZeroFree_extDeriv_eq_zero
    (s : EntireXiZeroFreePoint) :
    extDeriv entireRiemannXiLogDifferentialForm s.1 = 0 := by
  exact entireRiemannXiLogDifferentialForm_extDeriv_eq_zero_actual s.1 s.2

@[simp] theorem entireRiemannXiLogDifferentialForm_apply
    (s : ℂ) (v : Fin 1 → ℂ) :
    entireRiemannXiLogDifferentialForm s v =
      entireRiemannXiLogOneForm s (v 0) := by
  simp [entireRiemannXiLogDifferentialForm]

theorem entireRiemannXiLogDifferentialForm_eq_actualRiemannXiLogOneForm
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (v : Fin 1 → ℂ) :
    entireRiemannXiLogDifferentialForm s v =
      ActualRiemannXiLogDerivativeBridge.actualRiemannXiLogOneForm
        s (v 0) := by
  rw [entireRiemannXiLogDifferentialForm_apply]
  rw [entireRiemannXiLogOneForm_eq_actualRiemannXiLogOneForm hs0 hs1]

theorem entireRiemannXiLogDifferentialForm_reflection_pullback
    (s : ℂ) (v : Fin 1 → ℂ) :
    entireRiemannXiLogDifferentialForm (1 - s) (fun _ => -(v 0)) =
      entireRiemannXiLogDifferentialForm s v := by
  change entireRiemannXiLogOneForm (1 - s) (-(v 0)) =
    entireRiemannXiLogOneForm s (v 0)
  exact entireRiemannXiLogOneForm_reflection_pullback s (v 0)

/-- The same form restricted to the actual zero-free subtype. -/
def entireRiemannXiLogDifferentialFormOnZeroFree
    (s : EntireXiZeroFreePoint) :
    ℂ [⋀^Fin 1]→L[ℂ] ℂ :=
  entireRiemannXiLogDifferentialForm s.1

@[simp] theorem entireRiemannXiLogDifferentialFormOnZeroFree_apply
    (s : EntireXiZeroFreePoint) (v : Fin 1 → ℂ) :
    entireRiemannXiLogDifferentialFormOnZeroFree s v =
      entireRiemannXiLogOneFormOnZeroFree s (v 0) := by
  simp [entireRiemannXiLogDifferentialFormOnZeroFree,
    entireRiemannXiLogDifferentialForm]

theorem entireRiemannXiLogDifferentialFormOnZeroFree_reflection_pullback
    (s : EntireXiZeroFreePoint) (v : Fin 1 → ℂ) :
    entireRiemannXiLogDifferentialFormOnZeroFree (reflectZeroFree s)
        (fun _ => -(v 0)) =
      entireRiemannXiLogDifferentialFormOnZeroFree s v := by
  simpa [entireRiemannXiLogDifferentialFormOnZeroFree, reflectZeroFree] using
    (entireRiemannXiLogDifferentialForm_reflection_pullback s.1 v)

theorem entireRiemannXiLogDifferentialFormOnZeroFree_conjugation_pullback
    (s : EntireXiZeroFreePoint) (v : Fin 1 → ℂ) :
    entireRiemannXiLogDifferentialFormOnZeroFree (conjugateZeroFree s)
        (fun _ => star (v 0)) =
      star (entireRiemannXiLogDifferentialFormOnZeroFree s v) := by
  change entireRiemannXiLogOneFormOnZeroFree
      (conjugateZeroFree s) (star (v 0)) =
    star (entireRiemannXiLogOneFormOnZeroFree s (v 0))
  exact entireRiemannXiLogOneFormOnZeroFree_conjugation_pullback s (v 0)

end InfoGeometry.Canonical.ActualEntireRiemannXiDifferentialFormBridge
