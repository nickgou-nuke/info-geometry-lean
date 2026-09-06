import Mathlib.Tactic
import InfoGeometry.Canonical.MetriplecticCore
import InfoGeometry.SuperMetriplectic.Flow
import InfoGeometry.Canonical.CategoricalRiemannMasterSynthesisBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Metriplectic quadratic and fixed-locus readouts

This module packages a finite Onsager quadratic form and an affine fixed-locus
readout.  It does not define a time-dependent flow or a convergence theorem.

1. A force vector obtained from the supplied energy and entropy force data.

2. A negative quadratic dissipation readout, nonpositive by the supplied
   Onsager nonnegativity premise.

3. An exact equivalence between vanishing of that readout and vanishing of
   the quadratic form.

4. A fixed-locus consequence for the affine reflection on `ℝ × ℝ`.

No analytic free-energy functional, flow, or spinor identification is
inferred from these definitions.
-/

namespace InfoGeometry.Canonical.MetriplecticSpinorFreeEnergyBridge

open InfoGeometry.SuperMetriplectic
open InfoGeometry.Canonical.CategoricalRiemannMasterSynthesisBridge

/-- Metriplectic free energy data structure. -/
structure MetriplecticFreeEnergyData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  onsagerData : OnsagerMetricData V
  energyForce : V
  entropyForce : V
  temperature : ℝ
  temperature_pos : 0 < temperature

/-- Total thermodynamic force driving the free energy flow: $\delta F = \delta H - T \cdot \delta S$. -/
def freeEnergyForce {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : MetriplecticFreeEnergyData V) : V :=
  data.energyForce - data.temperature • data.entropyForce

/-- Free energy dissipation rate along the metriplectic flow: $\frac{\mathrm{d}F}{\mathrm{d}t} = -\langle \delta F, \mathbf{L}(\delta F) \rangle$. -/
def freeEnergyDissipationRate {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : MetriplecticFreeEnergyData V) : ℝ :=
  - data.onsagerData.quadratic (freeEnergyForce data)

/--
**Nonpositive quadratic dissipation readout.**
The defined negative quadratic form is nonpositive:
$$\frac{\mathrm{d}F}{\mathrm{d}t} \le 0.$$
-/
theorem free_energy_dissipation_nonpos {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : MetriplecticFreeEnergyData V) :
    freeEnergyDissipationRate data ≤ 0 := by
  unfold freeEnergyDissipationRate
  have h_quad := data.onsagerData.quadratic_nonnegative (freeEnergyForce data)
  linarith

/--
**Vanishing readout equivalence.**
The dissipation readout vanishes exactly when the quadratic form vanishes.
-/
theorem free_energy_equilibrium_iff_zero_quadratic {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : MetriplecticFreeEnergyData V) :
    freeEnergyDissipationRate data = 0 ↔ data.onsagerData.quadratic (freeEnergyForce data) = 0 := by
  unfold freeEnergyDissipationRate
  constructor
  · intro h; linarith
  · intro h; linarith

/--
**Affine fixed-locus consequence.**
An assumed fixed point of the affine reflection has first coordinate `1/2`.
-/
theorem spinor_fixed_locus_equilibrium_alignment (v : ℝ × ℝ) (h_eq : realAntiunitaryReflection v = v) :
    v.1 = 1 / 2 :=
  (realAntiunitaryReflection_fixed_locus v).mp h_eq

end InfoGeometry.Canonical.MetriplecticSpinorFreeEnergyBridge
