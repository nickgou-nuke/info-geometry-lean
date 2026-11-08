import InfoGeometry.Topology.ThermodynamicSL2MobiusFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Real Jacobian and log-Jacobian surprisal for the finite Mobius flow

The upstream Mobius owner exposes the complex derivative and its
multiplicative cocycle.  This file records the corresponding real two
dimensional Jacobian density as `‖f'‖²` and its negative logarithm.  No
topological degree, measure-theoretic Radon--Nikodym theorem, or physical
interpretation is asserted here.
-/

noncomputable section

namespace InfoGeometry.Topology.MobiusLogJacobianSurprisalBridge

open InfoGeometry.Topology.ThermodynamicSL2MobiusFlow
open InfoGeometry.Topology.ThermodynamicSL2MobiusFlow.ThermodynamicSL2Variation

def mobiusJacobianDensity
    (v : ThermodynamicSL2Variation) (t z : ℂ) : ℝ :=
  ‖v.finiteOrbitJacobian t z‖ * ‖v.finiteOrbitJacobian t z‖

def mobiusLogJacobianSurprisal
    (v : ThermodynamicSL2Variation) (t z : ℂ) : ℝ :=
  -Real.log (mobiusJacobianDensity v t z)

theorem mobiusJacobianDensity_eq_square
    (v : ThermodynamicSL2Variation) (t z : ℂ) :
    mobiusJacobianDensity v t z =
      ‖v.finiteOrbitJacobian t z‖ ^ (2 : ℕ) := by
  simp [mobiusJacobianDensity, pow_two]

theorem mobiusJacobianDensity_ne_zero
    (v : ThermodynamicSL2Variation) (t z : ℂ)
    (hden : v.finiteOrbitDenominator t z ≠ 0) :
    mobiusJacobianDensity v t z ≠ 0 := by
  unfold mobiusJacobianDensity
  have hJ : v.finiteOrbitJacobian t z ≠ 0 :=
    v.finiteOrbitJacobian_ne_zero t z hden
  exact mul_ne_zero (norm_ne_zero_iff.mpr hJ) (norm_ne_zero_iff.mpr hJ)

theorem mobiusLogJacobianSurprisal_eq_neg_two_logNorm
    (v : ThermodynamicSL2Variation) (t z : ℂ)
    (hden : v.finiteOrbitDenominator t z ≠ 0) :
    mobiusLogJacobianSurprisal v t z =
      -2 * v.logJacobianNorm t z := by
  unfold mobiusLogJacobianSurprisal logJacobianNorm
  rw [mobiusJacobianDensity, Real.log_mul]
  · ring
  · exact norm_ne_zero_iff.mpr (v.finiteOrbitJacobian_ne_zero t z hden)
  · exact norm_ne_zero_iff.mpr (v.finiteOrbitJacobian_ne_zero t z hden)

theorem mobiusJacobianDensity_add
    (v : ThermodynamicSL2Variation) (s t z : ℂ)
    (hinner : v.finiteOrbitDenominator t z ≠ 0)
    (houter : v.finiteOrbitDenominator s (v.finiteOrbit t z) ≠ 0) :
    mobiusJacobianDensity v (s + t) z =
      mobiusJacobianDensity v s (v.finiteOrbit t z) *
        mobiusJacobianDensity v t z := by
  unfold mobiusJacobianDensity
  rw [v.finiteOrbitJacobian_add s t z hinner, norm_mul]
  ring

theorem mobiusLogJacobianSurprisal_add
    (v : ThermodynamicSL2Variation) (s t z : ℂ)
    (hinner : v.finiteOrbitDenominator t z ≠ 0)
    (houter : v.finiteOrbitDenominator s (v.finiteOrbit t z) ≠ 0) :
    mobiusLogJacobianSurprisal v (s + t) z =
      mobiusLogJacobianSurprisal v s (v.finiteOrbit t z) +
        mobiusLogJacobianSurprisal v t z := by
  unfold mobiusLogJacobianSurprisal
  rw [mobiusJacobianDensity_add v s t z hinner houter, Real.log_mul]
  · ring
  · exact mobiusJacobianDensity_ne_zero v s (v.finiteOrbit t z) houter
  · exact mobiusJacobianDensity_ne_zero v t z hinner

end InfoGeometry.Topology.MobiusLogJacobianSurprisalBridge
