/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Native contact forms for the real Beltrami shear

The metric momentum of the existing real spatial field is the native one-form
`alpha_s = cos(z) dx - s sin(z) dy`. Its exterior derivative is computed from
an actual Frechet derivative, and its contact volume is the native alternating
form `alpha_s wedge d alpha_s = s dx wedge dy wedge dz`.

For the two signs `s ^ 2 = 1`, the existing velocity satisfies the Reeb equations
and its actual particle flow preserves the one-form by derivative pullback.
The contact-volume coefficient equals the already constructed physical neutral
pairing and local helicity. Constant rescaling of the contact form has weight two
in this three-dimensional example; this is distinct from the weight-three
Jacobian of a spatial dilation.

These are concrete forms on the existing real coordinate space. No general
contact-manifold structure, full SDiff Lie group, or global Euler geodesic
construction is asserted.
-/

noncomputable section

open scoped ContDiff

namespace InfoGeometry.Canonical.ArnoldBeltramiContact

open InfoGeometry.Canonical.NavierStokesShearReconstruction
open InfoGeometry.Canonical.ArnoldBeltramiFlow
open InfoGeometry.Canonical.ArnoldBeltramiCotangentTransport
open InfoGeometry.Quantum.DualFlatKreinGraph

/-- The actual metric momentum, written as a continuous linear covector on the
existing spatial coordinate carrier. -/
def momentumCLM (s : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  Real.cos (x 2) • ContinuousLinearMap.proj 0 -
    (s * Real.sin (x 2)) • ContinuousLinearMap.proj 1

@[simp] theorem momentumCLM_apply (s : ℝ) (x v : Space) :
    momentumCLM s x v = Real.cos (x 2) * v 0 - s * Real.sin (x 2) * v 1 := by
  simp [momentumCLM]

/-- The new continuous covector is the existing physical momentum, in spatial
coordinates. -/
theorem momentumCLM_eq_momentum (s : ℝ) (x v : Space) :
    momentumCLM s x v = momentum s x (coordinateEuclidean v) := by
  rw [momentumCLM_apply, momentum_apply]
  rfl

/-- Mathlib's native linear isometric identification of covectors and 1-forms. -/
def covectorToOneForm :
    (Space →L[ℝ] ℝ) →L[ℝ] Space [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ)
    (0 : Fin 1)).toLinearIsometry.toContinuousLinearMap

@[simp] theorem covectorToOneForm_apply (a : Space →L[ℝ] ℝ)
    (v : Fin 1 → Space) : covectorToOneForm a v = a (v 0) := rfl

/-- The actual momentum as a native differential 1-form. -/
def momentumForm (s : ℝ) : Space → Space [⋀^Fin 1]→L[ℝ] ℝ :=
  fun x => covectorToOneForm (momentumCLM s x)

@[simp] theorem momentumForm_apply (s : ℝ) (x : Space) (v : Fin 1 → Space) :
    momentumForm s x v = momentumCLM s x (v 0) := rfl

/-- Smoothness is inherited from the actual trigonometric coefficients. -/
theorem contDiff_momentumCLM (s : ℝ) : ContDiff ℝ ∞ (momentumCLM s) := by
  unfold momentumCLM
  fun_prop

theorem contDiff_momentumForm (s : ℝ) : ContDiff ℝ ∞ (momentumForm s) :=
  covectorToOneForm.contDiff.comp (contDiff_momentumCLM s)

/-- The continuous linear derivative of the covector-valued momentum map. -/
def momentumDerivative (s : ℝ) (x : Space) : Space →L[ℝ] (Space →L[ℝ] ℝ) :=
  (ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ).smulRight
    ((-Real.sin (x 2)) • ContinuousLinearMap.proj 0 -
      (s * Real.cos (x 2)) • ContinuousLinearMap.proj 1)

@[simp] theorem momentumDerivative_apply (s : ℝ) (x v w : Space) :
    momentumDerivative s x v w =
      -Real.sin (x 2) * v 2 * w 0 - s * Real.cos (x 2) * v 2 * w 1 := by
  simp [momentumDerivative]
  ring

/-- A native derivative witness, derived by trigonometric and scalar-product
rules, rather than supplied as a field. -/
theorem hasFDerivAt_momentumCLM (s : ℝ) (x : Space) :
    HasFDerivAt (momentumCLM s) (momentumDerivative s x) x := by
  have hcos := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x).cos
  have hsin := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x).sin
  have h : HasFDerivAt (momentumCLM s)
      (((-Real.sin (x 2)) • (ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ)).smulRight
        (ContinuousLinearMap.proj 0 : Space →L[ℝ] ℝ) -
        ((s * Real.cos (x 2)) • (ContinuousLinearMap.proj 2 : Space →L[ℝ] ℝ)).smulRight
          (ContinuousLinearMap.proj 1 : Space →L[ℝ] ℝ)) x := by
    convert!
      (hcos.smul_const (ContinuousLinearMap.proj 0 : Space →L[ℝ] ℝ)).fun_sub
        ((hsin.fun_const_smul s).smul_const
          (ContinuousLinearMap.proj 1 : Space →L[ℝ] ℝ)) using 1
    simp only [smul_smul]
  apply h.congr_fderiv
  ext v w
  simp [momentumDerivative]
  ring

theorem hasFDerivAt_momentumForm (s : ℝ) (x : Space) :
    HasFDerivAt (momentumForm s)
      (covectorToOneForm.comp (momentumDerivative s x)) x :=
  covectorToOneForm.hasFDerivAt.comp x (hasFDerivAt_momentumCLM s x)

theorem fderiv_momentumForm (s : ℝ) (x : Space) :
    fderiv ℝ (momentumForm s) x =
      covectorToOneForm.comp (momentumDerivative s x) :=
  (hasFDerivAt_momentumForm s x).fderiv

/-- Evaluation of the actual exterior derivative on an arbitrary pair of
spatial tangent vectors. -/
theorem extDeriv_momentumForm_apply (s : ℝ) (x : Space) (v : Fin 2 → Space) :
    extDeriv (momentumForm s) x v =
      -Real.sin (x 2) * (v 0 2 * v 1 0 - v 0 0 * v 1 2) -
        s * Real.cos (x 2) * (v 0 2 * v 1 1 - v 0 1 * v 1 2) := by
  rw [extDeriv, fderiv_momentumForm,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two]
  simp [covectorToOneForm_apply, momentumDerivative_apply, Fin.removeNth, Fin.tail]
  ring

/-- Native wedge of a covector and a two-form, using Mathlib's alternating
uncurrying operation. Its normalization is the usual three-term wedge. -/
def oneWedgeTwo (a : Space →L[ℝ] ℝ) (b : Space [⋀^Fin 2]→L[ℝ] ℝ) :
    Space [⋀^Fin 3]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin (a.smulRight b)

theorem oneWedgeTwo_apply (a : Space →L[ℝ] ℝ) (b : Space [⋀^Fin 2]→L[ℝ] ℝ)
    (v : Fin 3 → Space) :
    oneWedgeTwo a b v =
      a (v 0) * b ![v 1, v 2] - a (v 1) * b ![v 0, v 2] +
        a (v 2) * b ![v 0, v 1] := by
  have h0 : (0 : Fin 3).removeNth v = ![v 1, v 2] := by
    ext i
    fin_cases i <;> rfl
  have h1 : (1 : Fin 3).removeNth v = ![v 0, v 2] := by
    ext i
    fin_cases i <;> rfl
  have h2 : (2 : Fin 3).removeNth v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  rw [oneWedgeTwo, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_three, h0, h1, h2]
  simp
  ring

/-- The actual native contact-volume form `alpha_s wedge d alpha_s`. -/
def contactVolume (s : ℝ) (x : Space) : Space [⋀^Fin 3]→L[ℝ] ℝ :=
  oneWedgeTwo (momentumCLM s x) (extDeriv (momentumForm s) x)

/-- The contact-volume evaluation is the signed spatial determinant, on every
frame. In particular, contactness follows without a unit-sign hypothesis. -/
theorem contactVolume_apply (s : ℝ) (x : Space) (v : Fin 3 → Space) :
    contactVolume s x v = s * Matrix.det v := by
  rw [contactVolume, oneWedgeTwo_apply]
  simp only [momentumCLM_apply, extDeriv_momentumForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = s * (Real.sin (x 2) ^ 2 + Real.cos (x 2) ^ 2) * Matrix.det v := by
      rw [Matrix.det_fin_three (fun i j => v i j)]
      ring
    _ = s * Matrix.det v := by
      rw [Real.sin_sq_add_cos_sq]
      ring

/-- The native coordinate frame, represented as the identity matrix. -/
def coordinateFrame : Fin 3 → Space := (1 : Matrix (Fin 3) (Fin 3) ℝ)

@[simp] theorem contactVolume_coordinateFrame (s : ℝ) (x : Space) :
    contactVolume s x coordinateFrame = s := by
  rw [contactVolume_apply]
  simp [coordinateFrame]

/-- The contact volume is nonzero at every point when the parameter is nonzero. -/
theorem contactVolume_ne_zero {s : ℝ} (hs : s ≠ 0) (x : Space) :
    contactVolume s x ≠ 0 := by
  intro h
  have hframe := congrArg
    (fun a : Space [⋀^Fin 3]→L[ℝ] ℝ => a coordinateFrame) h
  exact hs (by simpa using hframe)

/-- The native contact-volume coefficient is the existing physical helicity
readout of the actual curl and metric momentum. -/
theorem contactVolume_eq_physicalNeutralPair (s : ℝ) (x : Space) :
    contactVolume s x coordinateFrame =
      neutralPair (physicalState s x) (physicalState s x) := by
  rw [contactVolume_coordinateFrame, neutralPair_physicalState]

/-- The unit-sign velocity satisfies the normalization half of the Reeb
equations for the actual native one-form. -/
theorem momentumForm_velocity {s : ℝ} (hs : s ^ 2 = 1) (x : Space) :
    momentumForm s x (fun _ => velocity s x) = 1 := by
  rw [momentumForm_apply, momentumCLM_eq_momentum]
  exact momentum_velocity hs x

/-- The unit-sign velocity annihilates the actual exterior derivative. -/
theorem extDeriv_momentumForm_velocity {s : ℝ} (hs : s ^ 2 = 1)
    (x v : Space) :
    extDeriv (momentumForm s) x ![velocity s x, v] = 0 := by
  rw [extDeriv_momentumForm_apply]
  change -Real.sin (x 2) * (0 * v 0 - Real.cos (x 2) * v 2) -
    s * Real.cos (x 2) * (0 * v 1 - (-s * Real.sin (x 2)) * v 2) = 0
  calc
    _ = (1 - s ^ 2) * (Real.sin (x 2) * Real.cos (x 2) * v 2) := by ring
    _ = 0 := by rw [hs]; ring

/-- The actual velocity satisfies both Reeb equations, with contactness proved
from the same actual exterior derivative. -/
theorem velocity_reeb_equations {s : ℝ} (hs : s ^ 2 = 1) (x : Space) :
    contactVolume s x ≠ 0 ∧
      momentumForm s x (fun _ => velocity s x) = 1 ∧
      ∀ v : Space, extDeriv (momentumForm s) x ![velocity s x, v] = 0 := by
  have hs0 : s ≠ 0 := by
    intro hzero
    simp [hzero] at hs
  exact ⟨contactVolume_ne_zero hs0 x, momentumForm_velocity hs x,
    extDeriv_momentumForm_velocity hs x⟩

/-- Pullback of the actual momentum covector along the actual flow derivative. -/
theorem momentumCLM_flow_pullback {s : ℝ} (hs : s ^ 2 = 1)
    (t : ℝ) (x v : Space) :
    momentumCLM s (flow s t x) (fderiv ℝ (flow s t) x v) = momentumCLM s x v := by
  rw [fderiv_flow, flowDerivative_apply, momentumCLM_apply, momentumCLM_apply]
  simp only [flow_third, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = (Real.cos (x 2) * v 0 - s * Real.sin (x 2) * v 1) +
        (s ^ 2 - 1) * (t * Real.sin (x 2) * Real.cos (x 2) * v 2) := by ring
    _ = Real.cos (x 2) * v 0 - s * Real.sin (x 2) * v 1 := by rw [hs]; ring

/-- Strict contact pullback stated on Mathlib's native alternating 1-form. -/
theorem momentumForm_flow_pullback {s : ℝ} (hs : s ^ 2 = 1)
    (t : ℝ) (x : Space) :
    (momentumForm s (flow s t x)).compContinuousLinearMap (fderiv ℝ (flow s t) x) =
      momentumForm s x := by
  apply ContinuousAlternatingMap.ext
  intro v
  change momentumCLM s (flow s t x) (fderiv ℝ (flow s t) x (v 0)) =
    momentumCLM s x (v 0)
  exact momentumCLM_flow_pullback hs t x (v 0)

/-- Scaling both factors in this native wedge has degree two. -/
theorem oneWedgeTwo_smul (c : ℝ) (a : Space →L[ℝ] ℝ)
    (b : Space [⋀^Fin 2]→L[ℝ] ℝ) :
    oneWedgeTwo (c • a) (c • b) = c ^ 2 • oneWedgeTwo a b := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [oneWedgeTwo_apply, smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- Contact volume of the constantly rescaled actual momentum form. -/
def scaledContactVolume (c s : ℝ) (x : Space) : Space [⋀^Fin 3]→L[ℝ] ℝ :=
  oneWedgeTwo (c • momentumCLM s x) (extDeriv (c • momentumForm s) x)

/-- Constant form scaling changes contact volume with weight two. The
exterior derivative in this assertion is the actual native derivative. -/
theorem scaledContactVolume_eq (c s : ℝ) (x : Space) :
    scaledContactVolume c s x = c ^ 2 • contactVolume s x := by
  unfold scaledContactVolume contactVolume
  rw [extDeriv_smul, oneWedgeTwo_smul]

/-- A constant rescaling of the contact form has the reciprocal Reeb field. -/
def scaledReeb (c s : ℝ) (x : Space) : Space := c⁻¹ • velocity s x

theorem scaledMomentumForm_scaledReeb {s c : ℝ} (hs : s ^ 2 = 1)
    (hc : c ≠ 0) (x : Space) :
    (c • momentumForm s) x (fun _ => scaledReeb c s x) = 1 := by
  change c * momentumCLM s x (c⁻¹ • velocity s x) = 1
  rw [map_smul, smul_eq_mul, momentumCLM_eq_momentum, momentum_velocity hs]
  simp [hc]

theorem extDeriv_scaledMomentumForm_scaledReeb {s : ℝ} (hs : s ^ 2 = 1)
    (c : ℝ) (x v : Space) :
    extDeriv (c • momentumForm s) x ![scaledReeb c s x, v] = 0 := by
  rw [extDeriv_smul]
  change c * extDeriv (momentumForm s) x ![c⁻¹ • velocity s x, v] = 0
  have hscale :
      extDeriv (momentumForm s) x ![c⁻¹ • velocity s x, v] =
        c⁻¹ * extDeriv (momentumForm s) x ![velocity s x, v] := by
    exact (extDeriv (momentumForm s) x).toAlternatingMap.map_vecCons_smul
      ![v] c⁻¹ (velocity s x)
  rw [hscale, extDeriv_momentumForm_velocity hs]
  ring

end InfoGeometry.Canonical.ArnoldBeltramiContact
