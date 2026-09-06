import InfoGeometry.Arithmetic.ActualRiemannXiRegularityBridge
import InfoGeometry.Canonical.ZetaLogDerivativeDeRhamPeriodBridge
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Concrete logarithmic differential readout for `riemannXi`

This is the realization edge from the scalar logarithmic-differential
bookkeeping owner to Mathlib's concrete completed-zeta readout.  It proves
only the pointwise quotient identity and its functional-reflection law.
No zero set, contour integral, de Rham cohomology class, or multiplicity
theorem is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualRiemannXiLogDerivativeBridge

open Complex
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Arithmetic.ActualRiemannXiRegularityBridge
open InfoGeometry.Canonical.ZetaLogDerivativeDeRhamPeriod

/-- The concrete scalar coefficient `-xi'/xi` for Mathlib's `riemannXi`. -/
def actualRiemannXiLogDifferential (s : ℂ) : ℂ :=
  zetaLogDifferentialForm (riemannXi s) (deriv riemannXi s)

/-! A native one-form carrier on the complex tangent line.  This owner does
not attach a closedness or cohomology instance to the pointwise form. -/

noncomputable def actualRiemannXiLogOneForm (s : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRight
    (1 : ℂ →L[ℂ] ℂ) (actualRiemannXiLogDifferential s)

@[simp] theorem actualRiemannXiLogOneForm_apply (s v : ℂ) :
    actualRiemannXiLogOneForm s v =
      v * actualRiemannXiLogDifferential s := by
  simp [actualRiemannXiLogOneForm]

@[simp] theorem actualRiemannXiLogDifferential_eq (s : ℂ) :
    actualRiemannXiLogDifferential s =
      -(deriv riemannXi s / riemannXi s) := rfl

/-- The concrete logarithmic differential is anti-invariant under `s ↦ 1-s`.

This uses the actual derivative-level functional equation on the regular
locus; it is not a formal property of an arbitrary `CompletedXiData`. -/
theorem actualRiemannXiLogDifferential_one_sub
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    actualRiemannXiLogDifferential (1 - s) =
      -actualRiemannXiLogDifferential s := by
  dsimp [actualRiemannXiLogDifferential, zetaLogDifferentialForm]
  rw [riemannXi_logDerivative_one_sub hs0 hs1]

theorem actualRiemannXiLogOneForm_reflection_pullback
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (v : ℂ) :
    actualRiemannXiLogOneForm (1 - s) (-v) =
      actualRiemannXiLogOneForm s v := by
  rw [actualRiemannXiLogOneForm_apply,
    actualRiemannXiLogOneForm_apply,
    actualRiemannXiLogDifferential_one_sub hs0 hs1]
  ring

end InfoGeometry.Canonical.ActualRiemannXiLogDerivativeBridge
