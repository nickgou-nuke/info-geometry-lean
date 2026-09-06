import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Canonical.ActualRiemannXiLogDerivativeBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Regular-locus coherence of the two actual completed-xi readouts

Mathlib supplies both the pole-removed entire representative
`entireRiemannXi` and the regular-locus readout `riemannXi`.  The former is
pointwise equal to the latter away from `0` and `1`; this owner transports that
identity to derivatives and to the logarithmic differential.  No zero
multiplicity, contour, or de Rham statement is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiRegularLogDerivativeBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open InfoGeometry.Canonical.ActualRiemannXiLogDerivativeBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge

theorem deriv_entireRiemannXi_eq_deriv_riemannXi
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv entireRiemannXi s = deriv riemannXi s := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
  exact entireRiemannXi_eq_riemannXi hz0 hz1

theorem entireRiemannXiLogDifferential_eq_actualRiemannXiLogDifferential
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireRiemannXiLogDifferential s = actualRiemannXiLogDifferential s := by
  rw [entireRiemannXiLogDifferential_eq,
    actualRiemannXiLogDifferential_eq,
    deriv_entireRiemannXi_eq_deriv_riemannXi hs0 hs1,
    entireRiemannXi_eq_riemannXi hs0 hs1]

theorem entireRiemannXiLogOneForm_eq_actualRiemannXiLogOneForm
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    entireRiemannXiLogOneForm s = actualRiemannXiLogOneForm s := by
  ext v
  rw [entireRiemannXiLogOneForm_apply,
    actualRiemannXiLogOneForm_apply,
    entireRiemannXiLogDifferential_eq_actualRiemannXiLogDifferential hs0 hs1]

end InfoGeometry.Canonical.ActualEntireRiemannXiRegularLogDerivativeBridge
