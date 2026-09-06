import InfoGeometry.Canonical.ActualEntireRiemannXiDifferentialFormBridge

/-!
# The actual zero-free closed one-form datum for `riemannXi`

This owner packages the already proved pointwise `extDeriv` identity on the
typed zero-free domain.  It does not identify a de Rham cohomology group or
construct a global period class.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeClosedForm

open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiDifferentialFormBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLocus
open InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeLogDifferential

structure Datum where
  form : ℂ → ℂ [⋀^Fin 1]→L[ℂ] ℂ
  closed_on_zero_free :
    ∀ s : EntireXiZeroFreePoint, extDeriv form s.1 = 0
  reflection_pullback :
    ∀ (s : ℂ) (v : Fin 1 → ℂ),
      form (1 - s) (fun _ => -(v 0)) = form s v
  conjugation_pullback :
    ∀ (s : EntireXiZeroFreePoint) (v : Fin 1 → ℂ),
      form (conjugateZeroFree s) (fun _ => star (v 0)) =
        star (form s.1 v)

noncomputable def actual : Datum where
  form := entireRiemannXiLogDifferentialForm
  closed_on_zero_free := by
    intro s
    exact entireRiemannXiLogDifferentialFormOnZeroFree_extDeriv_eq_zero s
  reflection_pullback := by
    intro s v
    exact entireRiemannXiLogDifferentialForm_reflection_pullback s v
  conjugation_pullback := by
    intro s v
    exact entireRiemannXiLogDifferentialFormOnZeroFree_conjugation_pullback s v

@[simp] theorem actual_form :
    actual.form = entireRiemannXiLogDifferentialForm :=
  rfl

@[simp] theorem actual_form_apply (s : ℂ) (v : Fin 1 → ℂ) :
    actual.form s v = v 0 * entireRiemannXiLogDifferential s := by
  simpa only [actual_form] using
    entireRiemannXiLogDifferentialForm_apply s v

theorem actual_form_differentiableOn_zero_free :
    DifferentiableOn ℂ actual.form
      ActualEntireRiemannXiZeroFreeLocus.entireRiemannXiZeroFreeLocus := by
  simpa only [actual_form] using
    entireRiemannXiLogDifferentialForm_differentiableOn_zero_free

theorem actual_form_continuousOn_zero_free :
    ContinuousOn actual.form
      ActualEntireRiemannXiZeroFreeLocus.entireRiemannXiZeroFreeLocus := by
  exact actual_form_differentiableOn_zero_free.continuousOn

theorem actual_closed_on_zero_free (s : EntireXiZeroFreePoint) :
    extDeriv actual.form s.1 = 0 := by
  exact actual.closed_on_zero_free s

theorem actual_reflection_pullback (s : ℂ) (v : Fin 1 → ℂ) :
    actual.form (1 - s) (fun _ => -(v 0)) = actual.form s v := by
  exact actual.reflection_pullback s v

theorem actual_conjugation_pullback
    (s : EntireXiZeroFreePoint) (v : Fin 1 → ℂ) :
    actual.form (conjugateZeroFree s) (fun _ => star (v 0)) =
      star (actual.form s.1 v) := by
  exact actual.conjugation_pullback s v

end InfoGeometry.Canonical.ActualEntireRiemannXiZeroFreeClosedForm
