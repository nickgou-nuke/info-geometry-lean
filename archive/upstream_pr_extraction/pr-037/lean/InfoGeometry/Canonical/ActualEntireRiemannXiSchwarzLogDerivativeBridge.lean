import Mathlib.Analysis.Calculus.Deriv.Star
import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
import InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge

/-!
# Schwarz symmetry of the actual entire `riemannXi` logarithmic readout

This owner lifts the already-proved global Schwarz identity for the entire
completed xi representative to its complex derivative and to the associated
logarithmic coefficient.  It is a pointwise analytic identity only: no
zero-free restriction, differential-form closedness, residue theorem, or
de Rham cohomology class is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ActualEntireRiemannXiSchwarzLogDerivativeBridge

open Complex
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireSchwarzBridge
open InfoGeometry.Canonical.ActualEntireRiemannXiLogDerivativeBridge

theorem deriv_entireRiemannXi_conj (s : ℂ) :
    deriv entireRiemannXi (star s) =
      star (deriv entireRiemannXi s) := by
  have hderiv : HasDerivAt entireRiemannXi
      (deriv entireRiemannXi s) s :=
    (differentiable_entireRiemannXi s).hasDerivAt
  have hstar := HasDerivAt.star_conj hderiv
  have hcongr : HasDerivAt entireRiemannXi
      (star (deriv entireRiemannXi s)) (star s) := by
    apply hstar.congr_of_eventuallyEq
    filter_upwards [] with z
    change entireRiemannXi z = star (entireRiemannXi (star z))
    rw [entireRiemannXi_conj]
    simp
  exact hcongr.deriv

theorem entireRiemannXiLogDifferential_conj (s : ℂ) :
    entireRiemannXiLogDifferential (star s) =
      star (entireRiemannXiLogDifferential s) := by
  unfold entireRiemannXiLogDifferential
  rw [deriv_entireRiemannXi_conj, ← entireRiemannXi_conj]
  simp

theorem entireRiemannXiLogOneForm_conj (s v : ℂ) :
    entireRiemannXiLogOneForm (star s) (star v) =
      star (entireRiemannXiLogOneForm s v) := by
  rw [entireRiemannXiLogOneForm_apply,
    entireRiemannXiLogOneForm_apply,
    entireRiemannXiLogDifferential_conj]
  simp

end InfoGeometry.Canonical.ActualEntireRiemannXiSchwarzLogDerivativeBridge
