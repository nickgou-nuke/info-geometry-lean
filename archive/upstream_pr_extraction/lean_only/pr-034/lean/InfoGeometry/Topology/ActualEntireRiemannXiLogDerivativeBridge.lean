import InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
import InfoGeometry.Topology.ZetaLogDerivativeDeRhamPeriodBridge
import InfoGeometry.Topology.ActualRiemannXiLogDerivativeBridge

/-!
# Actual entire completed-Xi logarithmic-derivative readout

This owner transports the derivative-level reflection theorem for the native
entire representative `entireRiemannXi` to the coefficient
`-ξ'/ξ`.  The coefficient is totalized at zeros by Lean's division operation.
No contour integral, residue, zero multiplicity, or de Rham cohomology claim
is made here.
-/

noncomputable section

namespace InfoGeometry.Topology.ActualEntireRiemannXiLogDerivative

open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open scoped Topology
open Filter
open InfoGeometry.Topology.ZetaLogDerivativeDeRhamPeriod

/-- The actual entire-Xi logarithmic-derivative coefficient. -/
def actualEntireXiOmegaForm (s : ℂ) : ℂ :=
  omegaForm (entireRiemannXi s) (deriv entireRiemannXi s)

@[simp] theorem actualEntireXiOmegaForm_apply (s : ℂ) :
    actualEntireXiOmegaForm s =
      -(deriv entireRiemannXi s / entireRiemannXi s) := rfl

/-!
The affine functional reflection acts with the expected sign on the
logarithmic derivative.  This is global because `entireRiemannXi` is the
pole-removed entire representative.
-/
theorem actualEntireXiOmegaForm_one_sub (s : ℂ) :
    actualEntireXiOmegaForm (1 - s) =
      -actualEntireXiOmegaForm s := by
  unfold actualEntireXiOmegaForm omegaForm
  rw [deriv_entireRiemannXi_one_sub, entireRiemannXi_one_sub]
  ring

/-!
On the regular locus the entire and meromorphic readouts have the same
logarithmic-derivative coefficient.  The derivative equality is obtained
from equality on a neighbourhood, rather than by treating a pointwise
identity as a derivative identity.
-/
theorem actualEntireXiOmegaForm_eq_actualXiOmegaForm
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    actualEntireXiOmegaForm s =
      InfoGeometry.Topology.ActualRiemannXiLogDerivative.actualXiOmegaForm s := by
  have hEq : ∀ᶠ z in nhds s,
      entireRiemannXi z = InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi z := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
    exact entireRiemannXi_eq_riemannXi hz0 hz1
  have hEq' : ∀ᶠ z in nhds s,
      InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi z =
        entireRiemannXi z := by
    filter_upwards [hEq] with z hz
    exact hz.symm
  have hEntire : HasDerivAt entireRiemannXi
      (deriv entireRiemannXi s) s :=
    differentiable_entireRiemannXi.differentiableAt.hasDerivAt
  have hRiemann : HasDerivAt
      InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi
      (deriv InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi s) s := by
    exact (InfoGeometry.Arithmetic.RiemannZetaEquivalences.differentiableAt_riemannXi
      hs0 hs1).hasDerivAt
  have hDeriv : deriv entireRiemannXi s =
      deriv InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi s :=
    (hEntire.congr_of_eventuallyEq hEq').unique hRiemann
  change -(deriv entireRiemannXi s / entireRiemannXi s) =
    -(deriv InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi s /
      InfoGeometry.Arithmetic.RiemannZetaEquivalences.riemannXi s)
  rw [entireRiemannXi_eq_riemannXi hs0 hs1, hDeriv]

end InfoGeometry.Topology.ActualEntireRiemannXiLogDerivative
