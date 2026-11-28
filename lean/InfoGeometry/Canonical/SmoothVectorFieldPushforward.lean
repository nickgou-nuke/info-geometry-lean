/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SmoothDiffeomorphismDensityOrbit
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.VectorField

/-!
# Smooth diffeomorphisms acting on vector fields

The existing smooth subgroup acts by the actual Fréchet derivative. The
construction acts on all fields `E → E` and preserves smooth fields. It agrees
with Mathlib's vector-field pullback by the inverse diffeomorphism.
The action is activated with `open scoped VectorFieldPushforward`, so importing
this owner does not change an existing pointwise action on a function type.

Differentiating a conjugated one-parameter group at zero gives the pushforward
of its generator. The generator derivative is an explicit hypothesis; a mere
group homomorphism is not assumed to depend differentiably on time. In
particular, a flow centralizer fixes the generator. No converse from a fixed
generator to a fixed flow is asserted without an ODE uniqueness argument.
-/

noncomputable section

namespace InfoGeometry.Canonical

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine derivative pushforward action, with inverse basepoint. -/
abbrev smoothDiffeomorphismVectorFieldAction :
    MulAction (smoothDiffeomorphismSubgroup E) (E → E) where
  smul g X y := fderiv ℝ (g.val : E → E) (g.val.symm y) (X (g.val.symm y))
  one_smul X := by
    funext y
    change fderiv ℝ (id : E → E) y (X y) = X y
    simp only [fderiv_id, ContinuousLinearMap.id_apply]
  mul_smul g h X := by
    funext y
    change fderiv ℝ ((g.val : E → E) ∘ (h.val : E → E))
        (h.val.symm (g.val.symm y)) (X (h.val.symm (g.val.symm y))) =
      fderiv ℝ (g.val : E → E) (g.val.symm y)
        (fderiv ℝ (h.val : E → E) (h.val.symm (g.val.symm y))
          (X (h.val.symm (g.val.symm y))))
    rw [fderiv_comp _ (g.property.1.differentiable (by simp) _)
      (h.property.1.differentiable (by simp) _)]
    simp only [Homeomorph.apply_symm_apply, ContinuousLinearMap.comp_apply]

/-- The scalar-action projection is scoped explicitly because the pointwise
function action is a different existing `SMul` instance. -/
abbrev smoothDiffeomorphismVectorFieldSMul :
    SMul (smoothDiffeomorphismSubgroup E) (E → E) :=
  smoothDiffeomorphismVectorFieldAction.toSMul

scoped[VectorFieldPushforward] attribute [instance 2000]
  InfoGeometry.Canonical.smoothDiffeomorphismVectorFieldSMul
scoped[VectorFieldPushforward] attribute [instance 2000]
  InfoGeometry.Canonical.smoothDiffeomorphismVectorFieldAction

open scoped VectorFieldPushforward

@[simp] theorem smoothDiffeomorphism_smul_vectorField_apply
    (g : smoothDiffeomorphismSubgroup E) (X : E → E) (y : E) :
    (g • X) y = fderiv ℝ (g.val : E → E) (g.val.symm y) (X (g.val.symm y)) := rfl

/-- Smoothness is preserved by the derivative pushforward. -/
theorem contDiff_smoothDiffeomorphism_smul_vectorField
    (g : smoothDiffeomorphismSubgroup E) {X : E → E} (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (g • X) := by
  exact ((g.property.1.fderiv_right (by simp)).comp g.property.2).clm_apply
    (hX.comp g.property.2)

/-- The inverse of the actual derivative is the derivative of the inverse. -/
theorem smoothDiffeomorphism_fderiv_inverse
    (g : smoothDiffeomorphismSubgroup E) (x : E) :
    (fderiv ℝ (g.val : E → E) x).inverse =
      fderiv ℝ (g.val.symm : E → E) (g.val x) := by
  have hleft : (g.val : E → E) ∘ (g.val.symm : E → E) = id := by
    funext y
    exact g.val.apply_symm_apply y
  have hright : (g.val.symm : E → E) ∘ (g.val : E → E) = id := by
    funext y
    exact g.val.symm_apply_apply y
  apply ContinuousLinearMap.inverse_eq
  · have hc := fderiv_comp (g.val x)
      (g.property.1.differentiable (by simp) _)
      (g.property.2.differentiable (by simp) _)
    simpa only [hleft, fderiv_id, Homeomorph.symm_apply_apply] using hc.symm
  · have hc := fderiv_comp x
      (g.property.2.differentiable (by simp) _)
      (g.property.1.differentiable (by simp) _)
    simpa only [hright, fderiv_id] using hc.symm

/-- This action is Mathlib's pullback along the inverse, with no new
notion of vector field or generalized inverse. -/
theorem smoothDiffeomorphism_smul_vectorField_eq_pullback
    (g : smoothDiffeomorphismSubgroup E) (X : E → E) :
    g • X = VectorField.pullback ℝ (g.val.symm : E → E) X := by
  funext y
  change fderiv ℝ (g.val : E → E) (g.val.symm y) (X (g.val.symm y)) =
    (fderiv ℝ (g.val.symm : E → E) y).inverse (X (g.val.symm y))
  exact congrArg (fun A : E →L[ℝ] E => A (X (g.val.symm y)))
    (smoothDiffeomorphism_fderiv_inverse (g⁻¹) y).symm

/-- Pushforward is linear in the field; it does not turn composition of
diffeomorphisms into a commutative operation. -/
theorem smoothDiffeomorphism_smul_vectorField_add
    (g : smoothDiffeomorphismSubgroup E) (X Y : E → E) :
    g • (X + Y) = g • X + g • Y := by
  funext y
  simp only [smoothDiffeomorphism_smul_vectorField_apply, Pi.add_apply, map_add]

theorem smoothDiffeomorphism_smul_vectorField_real_smul
    (g : smoothDiffeomorphismSubgroup E) (a : ℝ) (X : E → E) :
    g • (a • X) = a • (g • X) := by
  funext y
  simp only [smoothDiffeomorphism_smul_vectorField_apply, Pi.smul_apply, map_smul]

/-- The genuine Lie bracket is natural under this action. The completeness
hypothesis belongs to the native pullback-bracket theorem being reused. -/
theorem smoothDiffeomorphism_smul_lieBracket [CompleteSpace E]
    (g : smoothDiffeomorphismSubgroup E) {X Y : E → E}
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) :
    g • VectorField.lieBracket ℝ X Y =
      VectorField.lieBracket ℝ (g • X) (g • Y) := by
  simp only [smoothDiffeomorphism_smul_vectorField_eq_pullback]
  funext y
  exact VectorField.pullback_lieBracket (n := ∞) (by simp)
    g.property.2.contDiffAt (hX _) (hY _)

/-- Differentiation of the conjugated flow intertwines conjugation with
the native derivative pushforward at time zero. -/
theorem hasDerivAt_conjugatedFlow_zero
    (g : smoothDiffeomorphismSubgroup E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) (X : E → E)
    (hΦ : ∀ x : E, HasDerivAt
      (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0)
    (y : E) :
    HasDerivAt
      (fun t : ℝ => (g * Φ (Multiplicative.ofAdd t) * g⁻¹).val y)
      ((g • X) y) 0 := by
  have hzero : g.val.symm y = (Φ (Multiplicative.ofAdd (0 : ℝ))).val (g.val.symm y) := by
    change g.val.symm y = (Φ 1).val (g.val.symm y)
    rw [map_one]
    rfl
  have hg := (g.property.1.differentiable (by simp) (g.val.symm y)).hasFDerivAt
  exact hg.comp_hasDerivAt_of_eq 0 (hΦ (g.val.symm y)) hzero

/-- Fixing the whole flow forces its derivative generator to be fixed.
The converse needs a separate uniqueness theorem for the flow equation. -/
theorem smoothDiffeomorphism_fixes_generator_of_fixes_flow
    (g : smoothDiffeomorphismSubgroup E)
    (Φ : Multiplicative ℝ →* smoothDiffeomorphismSubgroup E) (X : E → E)
    (hΦ : ∀ x : E, HasDerivAt
      (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val x) (X x) 0)
    (hconj : ∀ t : Multiplicative ℝ, g * Φ t * g⁻¹ = Φ t) :
    g • X = X := by
  funext y
  have hg := hasDerivAt_conjugatedFlow_zero g Φ X hΦ y
  have heq : (fun t : ℝ => (g * Φ (Multiplicative.ofAdd t) * g⁻¹).val y) =
      (fun t : ℝ => (Φ (Multiplicative.ofAdd t)).val y) := by
    funext t
    rw [hconj]
  rw [heq] at hg
  exact hg.unique (hΦ y)

end InfoGeometry.Canonical
