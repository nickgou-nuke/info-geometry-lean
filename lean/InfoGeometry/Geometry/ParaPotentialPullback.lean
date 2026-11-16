/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

/-!
# A potential on two coordinate factors from a scalar parameter potential

For a real normed space `E` and `f : E → ℝ`, the chosen map `(x,y) ↦ x+y`
defines `potential f (x,y) = f (x+y)`. Native Fréchet differentiation proves
that its mixed derivative is the Hessian of `f`, when the indicated derivatives
exist. The associated mixed bilinear form is symmetric, has isotropic factors,
and is nondegenerate when the Hessian separates both variables.

This is an explicit choice of parameter map, not a canonical identification of
spinors with temperatures. In particular its mixed neutral metric is different
from its full ordinary Hessian: the latter vanishes on `(u,-u)` directions.
No partition function, statistical state, group action, or manifold is assumed
or constructed by this module.
-/

noncomputable section

namespace InfoGeometry.Geometry.ParaPotentialPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The specified map from two coordinate factors to a parameter space. -/
def sumCoordinates : E × E →L[ℝ] E :=
  ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E

@[simp] theorem sumCoordinates_apply (X : E × E) :
    sumCoordinates X = X.1 + X.2 := rfl

/-- Pull back a scalar parameter potential along the sum of the two factors. -/
def potential (f : E → ℝ) (X : E × E) : ℝ := f (X.1 + X.2)

/-- The actual first Fréchet derivative of the chosen potential. -/
theorem hasFDerivAt_potential {f : E → ℝ} {df : E →L[ℝ] ℝ} (X : E × E)
    (hf : HasFDerivAt f df (X.1 + X.2)) :
    HasFDerivAt (potential f) (df.comp sumCoordinates) X :=
  hf.comp X (sumCoordinates (E := E)).hasFDerivAt

/-- Differentiation in the second coordinate factor is ordinary differentiation
of `f` at the sum of the coordinates. -/
theorem fderiv_second_factor {f : E → ℝ} (x y : E)
    (hf : DifferentiableAt ℝ f (x + y)) :
    fderiv ℝ (fun z : E => potential f (x, z)) y = fderiv ℝ f (x + y) := by
  have h := hf.hasFDerivAt.comp y ((hasFDerivAt_id y).const_add x)
  simpa only [potential, Function.comp_def, ContinuousLinearMap.comp_id] using h.fderiv

/-- The mixed second derivative is exactly the parameter Hessian.
The derivative hypothesis is a native `HasFDerivAt`, not a Hessian identity
stored in a new structure field. -/
theorem mixed_second_derivative {f : E → ℝ}
    (hf : Differentiable ℝ f) (x y u v : E)
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : HasFDerivAt (fderiv ℝ f) H (x + y)) :
    fderiv ℝ (fun z : E =>
      fderiv ℝ (fun w : E => potential f (z, w)) y v) x u = H u v := by
  have heq : (fun z : E =>
      fderiv ℝ (fun w : E => potential f (z, w)) y v) =
      (fun z : E => fderiv ℝ f (z + y) v) := by
    funext z
    rw [fderiv_second_factor z y (hf (z + y))]
  have hsum : HasFDerivAt (fun z : E => z + y)
      (ContinuousLinearMap.id ℝ E) x := (hasFDerivAt_id x).add_const y
  have hd : HasFDerivAt (fun z : E => fderiv ℝ f (z + y) v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp H) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.comp_id] using
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x (hH.comp x hsum))
  rw [heq, hd.fderiv]
  rfl

omit [NormedSpace ℝ E] in
/-- Opposite shifts of the two factors leave this potential unchanged. -/
theorem potential_opposite_shift (f : E → ℝ) (X : E × E) (u : E) :
    potential f (X + (u, -u)) = potential f X := by
  unfold potential
  congr 1
  change X.1 + u + (X.2 + -u) = X.1 + X.2
  abel

/-- The symmetric mixed form extracted from a parameter Hessian.
The order of arguments of `H` is explicit; symmetry of `H` is not assumed. -/
def mixedMetric (H : E →L[ℝ] E →L[ℝ] ℝ) (U V : E × E) : ℝ :=
  H U.1 V.2 + H V.1 U.2

/-- The fundamental alternating form for the signed coordinate polarization. -/
def mixedOmega (H : E →L[ℝ] E →L[ℝ] ℝ) (U V : E × E) : ℝ :=
  H U.1 V.2 - H V.1 U.2

theorem mixedMetric_symmetric (H : E →L[ℝ] E →L[ℝ] ℝ) (U V : E × E) :
    mixedMetric H U V = mixedMetric H V U := by
  unfold mixedMetric
  exact add_comm _ _

theorem mixedOmega_skew (H : E →L[ℝ] E →L[ℝ] ℝ) (U V : E × E) :
    mixedOmega H U V = -mixedOmega H V U := by
  unfold mixedOmega
  ring

@[simp] theorem mixedOmega_self (H : E →L[ℝ] E →L[ℝ] ℝ) (U : E × E) :
    mixedOmega H U U = 0 := by simp [mixedOmega]

theorem mixedMetric_para_anti_isometry
    (H : E →L[ℝ] E →L[ℝ] ℝ) (U V : E × E) :
    mixedMetric H (U.1, -U.2) (V.1, -V.2) = -mixedMetric H U V := by
  simp [mixedMetric, add_comm]

theorem mixedOmega_eq_metric_para
    (H : E →L[ℝ] E →L[ℝ] ℝ) (U V : E × E) :
    mixedOmega H U V = mixedMetric H (U.1, -U.2) V := by
  simp [mixedOmega, mixedMetric, sub_eq_add_neg]

@[simp] theorem mixedMetric_first_isotropic
    (H : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    mixedMetric H (u, 0) (v, 0) = 0 := by simp [mixedMetric]

@[simp] theorem mixedMetric_second_isotropic
    (H : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    mixedMetric H (0, u) (0, v) = 0 := by simp [mixedMetric]

/-- Separation of both arguments of `H` proves actual separation of the
mixed metric, by testing the two coordinate factors independently. -/
theorem mixedMetric_nondegenerate
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hleft : ∀ u, (∀ v, H u v = 0) → u = 0)
    (hright : ∀ v, (∀ u, H u v = 0) → v = 0)
    (U : E × E) (hU : ∀ V, mixedMetric H U V = 0) : U = 0 := by
  have h₁ : U.1 = 0 := by
    apply hleft U.1
    intro v
    simpa [mixedMetric] using hU (0, v)
  have h₂ : U.2 = 0 := by
    apply hright U.2
    intro u
    simpa [mixedMetric] using hU (u, 0)
  exact Prod.ext h₁ h₂

/-- The corresponding alternating form also separates points. -/
theorem mixedOmega_nondegenerate
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hleft : ∀ u, (∀ v, H u v = 0) → u = 0)
    (hright : ∀ v, (∀ u, H u v = 0) → v = 0)
    (U : E × E) (hU : ∀ V, mixedOmega H U V = 0) : U = 0 := by
  have h₁ : U.1 = 0 := by
    apply hleft U.1
    intro v
    simpa [mixedOmega] using hU (0, v)
  have h₂ : U.2 = 0 := by
    apply hright U.2
    intro u
    have h := hU (u, 0)
    simpa [mixedOmega] using h
  exact Prod.ext h₁ h₂

/-- The pullback of a Hessian bilinear form vanishes on an opposite direction.
This is an algebraic statement about the pullback, independently of the
mixed derivative theorem above. -/
theorem pullback_bilinear_opposite
    (H : E →L[ℝ] E →L[ℝ] ℝ) (u : E) (V : E × E) :
    H (sumCoordinates (u, -u)) (sumCoordinates V) = 0 := by simp

/-- Even for a positive parameter Hessian the mixed metric has negative
directions; positivity cannot be transferred by naming the two forms alike. -/
theorem mixedMetric_negative_direction
    (H : E →L[ℝ] E →L[ℝ] ℝ) (u : E) (hu : 0 < H u u) :
    mixedMetric H (u, -u) (u, -u) < 0 := by
  simp only [mixedMetric, map_neg]
  linarith only [hu]

end InfoGeometry.Geometry.ParaPotentialPullback
