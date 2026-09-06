import InfoGeometry.Canonical.ActualEntireCenteredXiBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Centered logarithmic readout for the actual entire completed xi

This owner transports the existing entire logarithmic differential and its
reflection pullback to `z = s - 1 / 2`.  It records only coefficient-level
analytic identities; no closed-form, contour-period, or de Rham-cohomology
instance is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireCenteredXiLogDerivativeBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge

/-- The actual entire logarithmic differential in centered coordinates. -/
def actualEntireCenteredXiLogDifferential (z : ℂ) : ℂ :=
  entireRiemannXiLogDifferential ((1 / 2 : ℂ) + z)

@[simp] theorem actualEntireCenteredXiLogDifferential_apply (z : ℂ) :
    actualEntireCenteredXiLogDifferential z =
      entireRiemannXiLogDifferential ((1 / 2 : ℂ) + z) := rfl

/-- The centered logarithmic coefficient is odd under centered reflection. -/
theorem actualEntireCenteredXiLogDifferential_neg (z : ℂ) :
    actualEntireCenteredXiLogDifferential (-z) =
      -actualEntireCenteredXiLogDifferential z := by
  unfold actualEntireCenteredXiLogDifferential
  have hcoord :
      (1 / 2 : ℂ) + (-z) = 1 - ((1 / 2 : ℂ) + z) := by
    ring
  rw [hcoord, entireRiemannXiLogDifferential_one_sub]

/-- The centered entire logarithmic one-form. -/
noncomputable def actualEntireCenteredXiLogOneForm (z : ℂ) : ℂ →L[ℂ] ℂ :=
  entireRiemannXiLogOneForm ((1 / 2 : ℂ) + z)

@[simp] theorem actualEntireCenteredXiLogOneForm_apply (z v : ℂ) :
    actualEntireCenteredXiLogOneForm z v =
      entireRiemannXiLogOneForm ((1 / 2 : ℂ) + z) v := rfl

/-- Centered reflection preserves the one-form after tangent pullback. -/
theorem actualEntireCenteredXiLogOneForm_reflection_pullback
    (z v : ℂ) :
    actualEntireCenteredXiLogOneForm (-z) (-v) =
      actualEntireCenteredXiLogOneForm z v := by
  unfold actualEntireCenteredXiLogOneForm
  have hcoord :
      (1 / 2 : ℂ) + (-z) = 1 - ((1 / 2 : ℂ) + z) := by
    ring
  rw [hcoord]
  exact entireRiemannXiLogOneForm_reflection_pullback _ v

end InfoGeometry.Canonical.ActualEntireCenteredXiLogDerivativeBridge
