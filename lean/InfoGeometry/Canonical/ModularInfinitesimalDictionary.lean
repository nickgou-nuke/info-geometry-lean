import Mathlib
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# Modular Infinitesimal Dictionary

Finite theorem surface for the common infinitesimal generator appearing as:

* logarithmic de Rham one-form `d log Q`,
* logarithmic Radon--Nikodym increment,
* infinitesimal Connes-cocycle generator,
* modular-Hamiltonian difference,
* Araki/Bregman first variation,
* logarithmic barrier force.

This file does not construct Type III von Neumann algebras, relative modular
operators, analytic cocycles, or de Rham cohomology.  It proves the finite
algebraic readouts from explicit named premises.

#### BUCKET 1: CLOSED FINITE THEOREMS
The modular-Hamiltonian difference, Connes generator, de Rham logarithmic form,
Araki/Bregman first variation, and barrier force agree with the stated signs
whenever the finite calibration equalities are supplied.  Vanishing of the
generator is equivalent to equality of the supplied modular Hamiltonians.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
Thermodynamic-gauge entropy production, monodromy/detailed-balance readouts,
and barrier-containment readouts depend only on explicitly named premises.

#### BUCKET 3: OPEN CLOSURE DEBT
None.  Analytic Connes cocycles, Araki relative entropy on von Neumann
algebras, and continuum monodromy theorems are intentionally outside this
finite file.
-/

namespace InfoGeometry.Canonical.ModularInfinitesimal

open ThermodynamicGauge

noncomputable section

universe u

/-- Modular-Hamiltonian difference `K_target - K_source`. -/
def modularHamiltonianDifference
    {Op : Type u} [Sub Op]
    (target source : Op) : Op :=
  target - source

/-- Araki/Bregman first variation sign convention: `- d log Q`. -/
def arakiBregmanGradient
    {Op : Type u} [Neg Op]
    (deRhamLogForm : Op) : Op :=
  -deRhamLogForm

/-- Self-concordant logarithmic barrier force sign convention: `- d log Q`. -/
def logarithmicBarrierForce
    {Op : Type u} [Neg Op]
    (deRhamLogForm : Op) : Op :=
  -deRhamLogForm

/--
If the log Radon--Nikodym increment and Connes generator are both calibrated
to the same modular-Hamiltonian difference, then they are equal.
-/
theorem connesGenerator_eq_logRadonNikodym
    {Op : Type u} [AddGroup Op]
    (logRadonNikodym connesGenerator targetHamiltonian sourceHamiltonian : Op)
    (hConnes :
      connesGenerator =
        modularHamiltonianDifference targetHamiltonian sourceHamiltonian)
    (hLogRN :
      logRadonNikodym =
        modularHamiltonianDifference targetHamiltonian sourceHamiltonian) :
    connesGenerator = logRadonNikodym := by
  rw [hConnes, hLogRN]

/--
If `d log Q` is calibrated to the logarithmic Radon--Nikodym increment, and the
Connes generator is calibrated to that same increment, then Connes equals
`d log Q`.
-/
theorem connesGenerator_eq_deRhamLogForm
    {Op : Type u} [AddGroup Op]
    (deRhamLogForm logRadonNikodym connesGenerator : Op)
    (hDeRham : deRhamLogForm = logRadonNikodym)
    (hConnes : connesGenerator = logRadonNikodym) :
    connesGenerator = deRhamLogForm := by
  rw [hConnes, ← hDeRham]

/-- The modular-Hamiltonian difference reads as `d log Q` under the supplied calibration. -/
theorem hamiltonianDifference_eq_deRhamLogForm
    {Op : Type u} [AddGroup Op]
    (deRhamLogForm logRadonNikodym targetHamiltonian sourceHamiltonian : Op)
    (hDeRham : deRhamLogForm = logRadonNikodym)
    (hLogRN :
      logRadonNikodym =
        modularHamiltonianDifference targetHamiltonian sourceHamiltonian) :
    modularHamiltonianDifference targetHamiltonian sourceHamiltonian =
      deRhamLogForm := by
  rw [← hLogRN, ← hDeRham]

/-- The Araki/Bregman first variation is minus the Connes generator. -/
theorem arakiGradient_eq_neg_connesGenerator
    {Op : Type u} [AddGroup Op]
    (deRhamLogForm connesGenerator : Op)
    (hConnes : connesGenerator = deRhamLogForm) :
    arakiBregmanGradient deRhamLogForm = -connesGenerator := by
  rw [hConnes]
  rfl

/-- The logarithmic barrier force is minus the Connes generator. -/
theorem barrierForce_eq_neg_connesGenerator
    {Op : Type u} [AddGroup Op]
    (deRhamLogForm connesGenerator : Op)
    (hConnes : connesGenerator = deRhamLogForm) :
    logarithmicBarrierForce deRhamLogForm = -connesGenerator := by
  rw [hConnes]
  rfl

/-- The Araki/Bregman first variation and the logarithmic barrier force agree. -/
theorem arakiGradient_eq_barrierForce
    {Op : Type u} [Neg Op]
    (deRhamLogForm : Op) :
    arakiBregmanGradient deRhamLogForm =
      logarithmicBarrierForce deRhamLogForm :=
  rfl

/-- Exact/detailed-balance sector: vanishing `d log Q` kills the Connes generator. -/
theorem connesGenerator_eq_zero_of_deRham_zero
    {Op : Type u} [Zero Op]
    (deRhamLogForm connesGenerator : Op)
    (hConnes : connesGenerator = deRhamLogForm)
    (hZero : deRhamLogForm = 0) :
    connesGenerator = 0 := by
  rw [hConnes, hZero]

/-- Vanishing modular-Hamiltonian difference forces equality of Hamiltonians. -/
theorem hamiltonians_equal_of_difference_zero
    {Op : Type u} [AddGroup Op]
    (targetHamiltonian sourceHamiltonian : Op)
    (hZero :
      modularHamiltonianDifference targetHamiltonian sourceHamiltonian = 0) :
    targetHamiltonian = sourceHamiltonian := by
  exact sub_eq_zero.mp hZero

/-- Equal modular Hamiltonians force a zero modular-Hamiltonian difference. -/
theorem difference_zero_of_hamiltonians_equal
    {Op : Type u} [AddGroup Op]
    (targetHamiltonian sourceHamiltonian : Op)
    (hEqual : targetHamiltonian = sourceHamiltonian) :
    modularHamiltonianDifference targetHamiltonian sourceHamiltonian = 0 := by
  rw [modularHamiltonianDifference, hEqual, sub_self]

/-- Vanishing Connes generator forces equality of the supplied modular Hamiltonians. -/
theorem hamiltonians_equal_of_connesGenerator_zero
    {Op : Type u} [AddGroup Op]
    (connesGenerator targetHamiltonian sourceHamiltonian : Op)
    (hConnes :
      connesGenerator =
        modularHamiltonianDifference targetHamiltonian sourceHamiltonian)
    (hZero : connesGenerator = 0) :
    targetHamiltonian = sourceHamiltonian := by
  apply hamiltonians_equal_of_difference_zero
  rw [← hConnes, hZero]

/-- Zero Connes generator iff the supplied modular Hamiltonians agree. -/
theorem connesGenerator_zero_iff_hamiltonians_equal
    {Op : Type u} [AddGroup Op]
    (connesGenerator targetHamiltonian sourceHamiltonian : Op)
    (hConnes :
      connesGenerator =
        modularHamiltonianDifference targetHamiltonian sourceHamiltonian) :
    connesGenerator = 0 ↔ targetHamiltonian = sourceHamiltonian := by
  constructor
  · intro hZero
    exact hamiltonians_equal_of_connesGenerator_zero
      connesGenerator targetHamiltonian sourceHamiltonian hConnes hZero
  · intro hEqual
    rw [hConnes]
    exact difference_zero_of_hamiltonians_equal
      targetHamiltonian sourceHamiltonian hEqual

/--
Thermodynamic-gauge readout: if the transition commutator is `d_ln_Q`, and the
Connes generator is calibrated to the same element, entropy production is the
Connes/modular infinitesimal.
-/
theorem entropyProduction_eq_connesGenerator_of_flow
    {Op : Type u} [Ring Op]
    (flow : CausalNonequilibriumFlow Op)
    (connesGenerator : Op)
    (hflow :
      flow.P_forward * flow.P_backward - flow.P_backward * flow.P_forward =
        flow.d_ln_Q)
    (hConnes : connesGenerator = flow.d_ln_Q) :
    entropy_production flow = connesGenerator := by
  rw [de_rham_potential_equals_entropy_production_of_commutator flow hflow]
  exact hConnes.symm

/-- A supplied first variation calibrated to the Araki/Bregman gradient is `-d log Q`. -/
theorem firstVariation_eq_neg_deRham
    {Op : Type u} [AddGroup Op]
    (firstVariation deRhamLogForm : Op)
    (hFirst : firstVariation = arakiBregmanGradient deRhamLogForm) :
    firstVariation = -deRhamLogForm := by
  rw [hFirst]
  rfl

/-- A supplied first variation calibrated to the Araki/Bregman gradient equals the barrier force. -/
theorem firstVariation_eq_barrierForce
    {Op : Type u} [Neg Op]
    (firstVariation deRhamLogForm : Op)
    (hFirst : firstVariation = arakiBregmanGradient deRhamLogForm) :
    firstVariation = logarithmicBarrierForce deRhamLogForm := by
  rw [hFirst]
  rfl

/-- A supplied first variation is minus the Connes generator once Connes is `d log Q`. -/
theorem firstVariation_eq_neg_connesGenerator
    {Op : Type u} [AddGroup Op]
    (firstVariation deRhamLogForm connesGenerator : Op)
    (hFirst : firstVariation = arakiBregmanGradient deRhamLogForm)
    (hConnes : connesGenerator = deRhamLogForm) :
    firstVariation = -connesGenerator := by
  rw [hFirst, hConnes]
  rfl

/-- A trivial loop premise kills `d log Q` through the supplied exactness implication. -/
theorem deRham_zero_of_trivialLoop
    {Op : Type u} [Zero Op]
    (trivialLoop exactConnection : Prop)
    (deRhamLogForm : Op)
    (hExact : trivialLoop → exactConnection)
    (hZero : exactConnection → deRhamLogForm = 0)
    (hLoop : trivialLoop) :
    deRhamLogForm = 0 :=
  hZero (hExact hLoop)

/-- A trivial loop kills the Connes generator under the supplied calibrations. -/
theorem connesGenerator_zero_of_trivialLoop
    {Op : Type u} [Zero Op]
    (trivialLoop exactConnection : Prop)
    (deRhamLogForm connesGenerator : Op)
    (hConnes : connesGenerator = deRhamLogForm)
    (hExact : trivialLoop → exactConnection)
    (hZero : exactConnection → deRhamLogForm = 0)
    (hLoop : trivialLoop) :
    connesGenerator = 0 :=
  connesGenerator_eq_zero_of_deRham_zero deRhamLogForm connesGenerator
    hConnes (deRham_zero_of_trivialLoop trivialLoop exactConnection
      deRhamLogForm hExact hZero hLoop)

/-- A trivial loop forces the supplied detailed-balance sector. -/
theorem detailedBalance_of_trivialLoop
    {Op : Type u} [Zero Op]
    (trivialLoop exactConnection detailedBalance : Prop)
    (deRhamLogForm connesGenerator : Op)
    (hConnes : connesGenerator = deRhamLogForm)
    (hExact : trivialLoop → exactConnection)
    (hZero : exactConnection → deRhamLogForm = 0)
    (hBalance : connesGenerator = 0 → detailedBalance)
    (hLoop : trivialLoop) :
    detailedBalance :=
  hBalance (connesGenerator_zero_of_trivialLoop trivialLoop exactConnection
    deRhamLogForm connesGenerator hConnes hExact hZero hLoop)

/-- Nonzero Connes generator is incompatible with a trivial loop. -/
theorem not_trivialLoop_of_connesGenerator_ne_zero
    {Op : Type u} [Zero Op]
    (trivialLoop exactConnection : Prop)
    (deRhamLogForm connesGenerator : Op)
    (hConnes : connesGenerator = deRhamLogForm)
    (hExact : trivialLoop → exactConnection)
    (hZero : exactConnection → deRhamLogForm = 0)
    (hNonzero : connesGenerator ≠ 0) :
    ¬ trivialLoop := by
  intro hLoop
  exact hNonzero (connesGenerator_zero_of_trivialLoop trivialLoop exactConnection
    deRhamLogForm connesGenerator hConnes hExact hZero hLoop)

end

end InfoGeometry.Canonical.ModularInfinitesimal
