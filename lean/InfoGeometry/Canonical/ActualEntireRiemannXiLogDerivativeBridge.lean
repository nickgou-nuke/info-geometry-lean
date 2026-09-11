import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Global logarithmic readout for the entire completed `riemannXi`

The regular `riemannXi` logarithmic differential is only identified away from
the exceptional points `0` and `1`.  The entire representative has a native
global quotient readout instead.  Division at zeros is Mathlib's totalized
field division; no pole, zero multiplicity, closedness, or de Rham class is
claimed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge

def entireRiemannXiLogDifferential (s : ℂ) : ℂ :=
  -(deriv entireRiemannXi s / entireRiemannXi s)

noncomputable def entireRiemannXiLogOneForm (s : ℂ) : ℂ →L[ℂ] ℂ :=
  ContinuousLinearMap.smulRight
    (1 : ℂ →L[ℂ] ℂ) (entireRiemannXiLogDifferential s)

@[simp] theorem entireRiemannXiLogOneForm_apply (s v : ℂ) :
    entireRiemannXiLogOneForm s v =
      v * entireRiemannXiLogDifferential s := by
  simp [entireRiemannXiLogOneForm]

@[simp] theorem entireRiemannXiLogDifferential_eq (s : ℂ) :
    entireRiemannXiLogDifferential s =
      -(deriv entireRiemannXi s / entireRiemannXi s) := rfl

theorem entireRiemannXiLogDifferential_one_sub (s : ℂ) :
    entireRiemannXiLogDifferential (1 - s) =
      -entireRiemannXiLogDifferential s := by
  dsimp [entireRiemannXiLogDifferential]
  rw [deriv_entireRiemannXi_one_sub, entireRiemannXi_one_sub]
  ring

theorem entireRiemannXiLogOneForm_reflection_pullback (s v : ℂ) :
    entireRiemannXiLogOneForm (1 - s) (-v) =
      entireRiemannXiLogOneForm s v := by
  rw [entireRiemannXiLogOneForm_apply,
    entireRiemannXiLogOneForm_apply,
    entireRiemannXiLogDifferential_one_sub]
  ring

end InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
