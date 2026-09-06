import Mathlib.Tactic
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangRHBridge
import InfoGeometry.Canonical.MetriplecticSpinorFreeEnergyBridge
import InfoGeometry.Canonical.DiracBerryKeatingFredholmBridge
import InfoGeometry.Canonical.ColimitRigidityProofChainBridge
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge
import InfoGeometry.Canonical.CategoricalRiemannRigidity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Finite Cayley and winding readouts

This module packages two finite algebraic readouts:

1. **Cayley alignment**: a unit-circle point away from the pole maps to the
   critical line.

2. **Finite winding readout**: a nonzero integer has nonzero charge
   `2 * π * n`.

No partition-function zero theorem, winding construction, phase transition,
or analytic Bost--Connes result is inferred by this file.
-/

namespace InfoGeometry.Canonical.LeeYangBostConnesPhaseTransitionBridge

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangRHBridge
open InfoGeometry.Canonical.MetriplecticSpinorFreeEnergyBridge
open InfoGeometry.Canonical.DiracBerryKeatingFredholmBridge
open InfoGeometry.Canonical.ColimitRigidityProofChainBridge
open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge
open InfoGeometry.Canonical.CategoricalRiemannRigidity

/-- Logarithmic potential wall condition at a partition function zero. -/
def HasLogarithmicPotentialWall (Z : ℂ → ℂ) (s0 : ℂ) : Prop :=
  Z s0 = 0

/-- de Rham topological winding charge around a phase transition zero. -/
noncomputable def TopologicalWindingCharge (n : ℤ) : ℝ :=
  2 * Real.pi * (n : ℝ)

/--
**Cayley alignment.**
If `z0` lies on the unit circle and avoids the pole, its Cayley temperature
lies on the critical line:
$$\|z_0\| = 1 \land z_0.re \neq -1 \implies \operatorname{Re}(\text{cayleyToTemperature } z_0) = \frac{1}{2}.$$
-/
theorem leeyang_zero_maps_to_critical_line {z0 : ℂ} (hz0 : OnLeeYangCircle z0) (hpole : z0.re ≠ -1) :
    OnCriticalLine (cayleyToTemperature z0) :=
  cayleyToTemperature_mem_criticalLine_of_unitCircle z0 hz0 hpole

/--
**Nonzero finite winding charge.**
For a nonzero integer `n`, the charge `2 * π * n` is nonzero:
$$n \neq 0 \implies 2\pi n \neq 0.$$
-/
theorem quantized_time_step_ne_zero {n : ℤ} (hn : n ≠ 0) :
    TopologicalWindingCharge n ≠ 0 := by
  unfold TopologicalWindingCharge
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn_real : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  exact mul_ne_zero (mul_ne_zero h2 hpi) hn_real

/--
**Finite conjunction of readouts.**
Combines Cayley alignment, nonzero winding charge, and a supplied fixed-locus
hypothesis.
-/
theorem grand_leeyang_bost_connes_phase_transition_master_duality
    (z0 : ℂ) (hz0 : OnLeeYangCircle z0) (hpole : z0.re ≠ -1)
    (n : ℤ) (hn : n ≠ 0) (s : ℂ) (h_anti : s = 1 - star s) :
    (OnCriticalLine (cayleyToTemperature z0)) ∧
    (TopologicalWindingCharge n ≠ 0) ∧
    (s.re = 1 / 2) ∧
    (s = 1 - star s) := by
  constructor
  · exact cayleyToTemperature_mem_criticalLine_of_unitCircle z0 hz0 hpole
  constructor
  · exact quantized_time_step_ne_zero hn
  constructor
  · exact (critical_line_fixed_locus_iff s).1 h_anti
  · exact h_anti

end InfoGeometry.Canonical.LeeYangBostConnesPhaseTransitionBridge
