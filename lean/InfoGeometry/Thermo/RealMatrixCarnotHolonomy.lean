/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.RealMatrixCarnotStateLoop
import InfoGeometry.Thermo.RealMatrixWorkConnection

/-! # Work-translation holonomy of the actual matrix Carnot cycle

The base retains both the full density matrix and its Hamiltonian control.
Each stroke pulls back the constructed work one-form to the actual trace
current. Native derivatives and interval FTC supply horizontal lifts; the
four integral transports compose to translation by work done on the system.
Under the established Carnot sign convention this translation is `-cycleWork`.

The inverse translation records work output and is nontrivial for a positive
entropy stroke with positive hot temperature and a colder positive reservoir.
This is an additive work-coordinate holonomy, not operator/Uhlmann phase.
The separate state-loop owner proves exact density retracing; projection to
density forgets the Hamiltonian scale that distinguishes these four base paths.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealMatrixCarnotHolonomy

open MeasureTheory RealMatrixCarnot RealMatrixWorkConnection
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Interval

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℝ

/-! ## Actual base paths and connection pullbacks -/

/-- The full Gibbs density and Hamiltonian along the affine isotherm. -/
def affineBaseCurve (β : ℝ) (H₀ H₁ : Mat) (t : ℝ) : Base n :=
  (state β (affineHamiltonian H₀ H₁ t), affineHamiltonian H₀ H₁ t)

/-- The actual state derivative and the proved affine Hamiltonian derivative. -/
def affineBaseVelocity (β : ℝ) (H₀ H₁ : Mat) (t : ℝ) : Base n :=
  (deriv (fun s => state β (affineHamiltonian H₀ H₁ s)) t, H₁ - H₀)

theorem hasDerivAt_affineBaseCurve [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) (t : ℝ) :
    HasDerivAt (affineBaseCurve β H₀ H₁) (affineBaseVelocity β H₀ H₁ t) t := by
  change HasDerivAt
    (fun s => (state β (affineHamiltonian H₀ H₁ s), affineHamiltonian H₀ H₁ s))
    (deriv (fun s => state β (affineHamiltonian H₀ H₁ s)) t, H₁ - H₀) t
  exact ((contDiff_state_affine β H₀ H₁ h₀ h₁).differentiable_one t).hasDerivAt.prodMk
    (hasDerivAt_affineHamiltonian H₀ H₁ t)

/-- The work connection pulls back to the previously constructed isothermal
current, with the density and Hamiltonian derivative in their original order. -/
theorem affineBase_workCurrent (β : ℝ) (H₀ H₁ : Mat) :
    workCurrent (affineBaseCurve β H₀ H₁) (affineBaseVelocity β H₀ H₁) =
      affineWorkCurrent β H₀ H₁ := by
  funext t
  rfl

/-- The full scale-stroke base curve: constant density and changing Hamiltonian. -/
def scalingBaseCurve (β a b : ℝ) (H : Mat) (t : ℝ) : Base n :=
  (state β H, scaleSegment a b t • H)

def scalingBaseVelocity (a b : ℝ) (H : Mat) (_t : ℝ) : Base n :=
  (0, (b - a) • H)

/-- On the physical unit interval this is exactly the Gibbs state obtained
from the changing reciprocal-temperature controls. -/
theorem scalingBaseCurve_eq_controls (β a b : ℝ) (H : Mat)
    (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    scalingBaseCurve β a b H t =
      (state (β / scaleSegment a b t) (scaleSegment a b t • H),
        scaleSegment a b t • H) := by
  exact Prod.ext (state_scaling_segment H β a b t ha hb ht).symm rfl

theorem hasDerivAt_scalingBaseCurve (β a b : ℝ) (H : Mat) (t : ℝ) :
    HasDerivAt (scalingBaseCurve β a b H) (scalingBaseVelocity a b H t) t := by
  change HasDerivAt (fun s => (state β H, scaleSegment a b s • H))
    (0, (b - a) • H) t
  exact (hasDerivAt_const t (state β H)).prodMk (hasDerivAt_scaledHamiltonian H a b t)

/-- The work current on a scale stroke, evaluated on its actual base velocity. -/
def scalingWorkCurrent (β a b : ℝ) (H : Mat) (_t : ℝ) : ℝ :=
  Matrix.trace (state β H * ((b - a) • H))

theorem scalingBase_workCurrent (β a b : ℝ) (H : Mat) :
    workCurrent (scalingBaseCurve β a b H) (scalingBaseVelocity a b H) =
      scalingWorkCurrent β a b H := by
  funext t
  rfl

/-- The generic constructed lift is horizontal on every affine Gibbs stroke;
its derivative premise is discharged by the actual matrix path. -/
theorem affineLift_horizontal [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) (w t : ℝ) :
    connectionForm
      (horizontalLift (affineBaseCurve β H₀ H₁) (affineBaseVelocity β H₀ H₁) 0 w t)
      (deriv (horizontalLift (affineBaseCurve β H₀ H₁)
        (affineBaseVelocity β H₀ H₁) 0 w) t) = 0 := by
  apply horizontalLift_horizontal
  · rw [affineBase_workCurrent]
    exact continuous_affineWorkCurrent β H₀ H₁ h₀ h₁
  · exact hasDerivAt_affineBaseCurve β H₀ H₁ h₀ h₁ t

/-- The scale stroke also has a constructed horizontal lift, including its
nonzero work current while the density is fixed. -/
theorem scalingLift_horizontal (β a b : ℝ) (H : Mat) (w t : ℝ) :
    connectionForm
      (horizontalLift (scalingBaseCurve β a b H) (scalingBaseVelocity a b H) 0 w t)
      (deriv (horizontalLift (scalingBaseCurve β a b H)
        (scalingBaseVelocity a b H) 0 w) t) = 0 := by
  apply horizontalLift_horizontal
  · rw [scalingBase_workCurrent]
    exact continuous_const
  · exact hasDerivAt_scalingBaseCurve β a b H t

/-! ## The closed full-base path -/

/-- The actual affine base curve as a native path, with both controls retained. -/
def affineBasePath [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    Path (state β H₀, H₀) (state β H₁, H₁) where
  toFun t := affineBaseCurve β H₀ H₁ (t : ℝ)
  continuous_toFun :=
    (continuous_iff_continuousAt.mpr (fun t =>
      (hasDerivAt_affineBaseCurve β H₀ H₁ h₀ h₁ t).continuousAt)).comp
        continuous_subtype_val
  source' := by simp [affineBaseCurve]
  target' := by simp [affineBaseCurve]

/-- The scale-stroke path retains its changing Hamiltonian. For positive
endpoint scales, its density agrees with the reciprocal Gibbs controls by
`scalingBaseCurve_eq_controls`. -/
def scalingBasePath (β a b : ℝ) (H : Mat) :
    Path (state β H, a • H) (state β H, b • H) where
  toFun t := scalingBaseCurve β a b H (t : ℝ)
  continuous_toFun :=
    (continuous_iff_continuousAt.mpr (fun t =>
      (hasDerivAt_scalingBaseCurve β a b H t).continuousAt)).comp
        continuous_subtype_val
  source' := by simp [scalingBaseCurve]
  target' := by simp [scalingBaseCurve]

/-- The actual cold affine base path, with its density endpoints identified
using the proved reciprocal-scale identity. -/
def coldBasePath [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hc : c ≠ 0) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    Path (state β H₁, c • H₁) (state β H₀, c • H₀) := by
  have h₀c : IsSelfAdjoint (c • H₀) := by
    rw [isSelfAdjoint_iff]
    simp [star_smul, h₀.star_eq]
  have h₁c : IsSelfAdjoint (c • H₁) := by
    rw [isSelfAdjoint_iff]
    simp [star_smul, h₁.star_eq]
  exact (affineBasePath (β / c) (c • H₁) (c • H₀) h₁c h₀c).cast
    (by simp [state_cold_corner β c H₁ hc])
    (by simp [state_cold_corner β c H₀ hc])

/-- The full four-stroke base path is closed in both density and Hamiltonian.
Endpoint matching is part of the native `Path` type, not a stored cycle law. -/
def baseCycle [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hc : 0 < c) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    Path (state β H₀, H₀) (state β H₀, H₀) :=
  (((affineBasePath β H₀ H₁ h₀ h₁).trans
      ((scalingBasePath β 1 c H₁).cast (by simp) rfl)).trans
      (coldBasePath β c H₀ H₁ hc.ne' h₀ h₁)).trans
      ((scalingBasePath β c 1 H₀).cast rfl (by simp))

/-! ## Four actual integral transports and their holonomy -/

/-- Chronological composition of the hot isotherm, first scale stroke,
cold isotherm and return scale stroke. Each factor integrates the actual
pulled-back matrix current rather than an assumed endpoint work budget. -/
def cycleWorkOnTransport (β c : ℝ) (H₀ H₁ : Mat) : ℝ ≃ᵃ[ℝ] ℝ :=
  (((workOnTransport (affineWorkCurrent β H₀ H₁) 0 1).trans
      (workOnTransport (scalingWorkCurrent β 1 c H₁) 0 1)).trans
      (workOnTransport (affineWorkCurrent (β / c) (c • H₁) (c • H₀)) 0 1)).trans
      (workOnTransport (scalingWorkCurrent β c 1 H₀) 0 1)

/-- The actual four-stroke connection transport shifts the work-on coordinate
by the negative of the established Carnot work output. -/
theorem cycleWorkOnTransport_apply [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) (w : ℝ) :
    cycleWorkOnTransport β c H₀ H₁ w = w - cycleWork β c H₀ H₁ := by
  simp only [cycleWorkOnTransport, AffineEquiv.trans_apply, workOnTransport_apply,
    scalingWorkCurrent]
  rw [affineWork_integral_eq_hotWorkOn β H₀ H₁ hβ h₀ h₁,
    affineWork_integral_eq_coldWorkOn β c H₀ H₁ hβ hc h₀ h₁,
    scalingWorkOn_integral β 1 c H₁, scalingWorkOn_integral β c 1 H₀]
  unfold cycleWork
  abel

/-- Holonomy as equality of native affine equivalences on the work fiber. -/
theorem cycleWorkOnTransport_eq_translation [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    cycleWorkOnTransport β c H₀ H₁ =
      AffineEquiv.constVAdd ℝ ℝ (-cycleWork β c H₀ H₁) := by
  ext w
  rw [cycleWorkOnTransport_apply β c H₀ H₁ hβ hc h₀ h₁]
  change w - cycleWork β c H₀ H₁ = -cycleWork β c H₀ H₁ + w
  abel

/-- The inverse fiber transport records work output rather than work-on. -/
theorem cycleWorkOnTransport_symm_apply [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) (w : ℝ) :
    (cycleWorkOnTransport β c H₀ H₁).symm w = w + cycleWork β c H₀ H₁ := by
  rw [cycleWorkOnTransport_eq_translation β c H₀ H₁ hβ hc h₀ h₁,
    AffineEquiv.constVAdd_symm, neg_neg]
  change cycleWork β c H₀ H₁ + w = w + cycleWork β c H₀ H₁
  exact add_comm _ _

/-- The Carnot entropy-area readback is derived from the native matrix
integrals. It is not a general Stokes theorem on an unspecified Souriau leaf. -/
theorem cycleWorkOnTransport_entropy_area [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) (w : ℝ) :
    cycleWorkOnTransport β c H₀ H₁ w =
      w - (1 / β - c / β) * (stateEntropy β H₁ - stateEntropy β H₀) := by
  rw [cycleWorkOnTransport_apply β c H₀ H₁ hβ hc h₀ h₁,
    cycleWork_eq_one_sub_scale_mul_hotHeat β c H₀ H₁ hβ hc]
  simp only [hotHeat, div_eq_mul_inv]
  ring

/-- Positive Carnot work makes the actual additive work holonomy nontrivial.
No nonzero operator phase is inferred from this real affine translation. -/
theorem cycleWorkOnTransport_ne_refl [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : 0 < β) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁)
    (hS : stateEntropy β H₀ < stateEntropy β H₁) :
    cycleWorkOnTransport β c H₀ H₁ ≠ AffineEquiv.refl ℝ ℝ := by
  intro h
  have hz := congrArg (fun e : ℝ ≃ᵃ[ℝ] ℝ => e 0) h
  rw [cycleWorkOnTransport_apply β c H₀ H₁ hβ.ne' hc.1.ne' h₀ h₁] at hz
  have hpos := cycleWork_pos β c H₀ H₁ hβ hc hS
  have hz' : (0 : ℝ) - cycleWork β c H₀ H₁ = 0 := hz
  linarith

end InfoGeometry.Thermo.RealMatrixCarnotHolonomy
