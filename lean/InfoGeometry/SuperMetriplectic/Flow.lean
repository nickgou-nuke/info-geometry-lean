import InfoGeometry.SuperMetriplectic.Blocks

/-!
# Supergraded Metriplectic Flow Packets

Abstract metriplectic flow layer for the supergraded program.

The file formalizes the part of the discussion that is independent of a
particular plasma, fluid, or conformal representation:

* reversible motion is kept separate from the Onsager/Fisher metric flow;
* the dissipative flow is `L dS`;
* energy degeneracy is the condition `L dH = 0`;
* entropy production is the body-level quadratic form `⟨dS, L dS⟩`;
* equilibrium means the entropy force lies in the null space of `L`.

All positivity, symmetry, and degeneracy facts are explicit fields of the
packet.  No analytic existence theorem is asserted here.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Linear Onsager data on a force space.

`pairing` is the body-level bilinear readout used to measure entropy production.
`onsager` maps thermodynamic forces to dissipative fluxes.  Symmetry and
positive-semidefiniteness are supplied as hypotheses of the packet.
-/
structure OnsagerMetricData
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  onsager : V →ₗ[ℝ] V
  pairing : V → V → ℝ
  metric_symmetric :
    ∀ x y : V, pairing x (onsager y) = pairing y (onsager x)
  metric_nonnegative :
    ∀ x : V, 0 ≤ pairing x (onsager x)
  pairing_zero_right :
    ∀ x : V, pairing x 0 = 0

namespace OnsagerMetricData

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Body-level Onsager quadratic form. -/
def quadratic (L : OnsagerMetricData V) (x : V) : ℝ :=
  L.pairing x (L.onsager x)

/-- The Onsager quadratic form is nonnegative by packet assumption. -/
theorem quadratic_nonnegative (L : OnsagerMetricData V) (x : V) :
    0 ≤ L.quadratic x :=
  L.metric_nonnegative x

end OnsagerMetricData

/--
Metriplectic flow packet.

`entropyForce` is `dS`, `energyForce` is `dH`, and `dissipativeFlow = L dS`.
The reversible flow is intentionally abstract: concrete Lie-Poisson/coadjoint
models can instantiate it with `ad*_(dH) Q`.
-/
structure MetriplecticFlow
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  metric : OnsagerMetricData V
  entropyForce : V
  energyForce : V
  reversibleFlow : V
  dissipativeFlow : V
  totalFlow : V
  entropyProduction : ℝ
  dissipativeFlow_eq_onsager_entropy :
    dissipativeFlow = metric.onsager entropyForce
  totalFlow_eq_reversible_add_dissipative :
    totalFlow = reversibleFlow + dissipativeFlow
  energy_degeneracy :
    metric.onsager energyForce = 0
  entropyProduction_eq_quadratic :
    entropyProduction = metric.pairing entropyForce dissipativeFlow

namespace MetriplecticFlow

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Entropy production is the Onsager quadratic form `⟨dS, L dS⟩`. -/
theorem entropyProduction_eq_onsager_quadratic
    (F : MetriplecticFlow V) :
    F.entropyProduction =
      F.metric.pairing F.entropyForce (F.metric.onsager F.entropyForce) := by
  rw [F.entropyProduction_eq_quadratic, F.dissipativeFlow_eq_onsager_entropy]

/-- The second-law inequality carried by the Onsager metric packet. -/
theorem entropyProduction_nonnegative
    (F : MetriplecticFlow V) :
    0 ≤ F.entropyProduction := by
  rw [F.entropyProduction_eq_onsager_quadratic]
  exact F.metric.metric_nonnegative F.entropyForce

/-!
The total metriplectic vector is the reversible vector plus the Onsager
response to the entropy force.  This is the canonical interface used by
concrete attention, Cuntz, and modular-flow realizations.
-/
theorem totalFlow_eq_reversible_add_onsager_entropy
    (F : MetriplecticFlow V) :
    F.totalFlow = F.reversibleFlow + F.metric.onsager F.entropyForce := by
  rw [F.totalFlow_eq_reversible_add_dissipative,
    F.dissipativeFlow_eq_onsager_entropy]

/--
Energy degeneracy of the dissipative flow:
`⟨dH, L dS⟩ = 0`, using metric symmetry and `L dH = 0`.
-/
theorem dissipative_energy_change_eq_zero
    (F : MetriplecticFlow V) :
    F.metric.pairing F.energyForce F.dissipativeFlow = 0 := by
  rw [F.dissipativeFlow_eq_onsager_entropy]
  rw [F.metric.metric_symmetric F.energyForce F.entropyForce]
  rw [F.energy_degeneracy]
  exact F.metric.pairing_zero_right F.entropyForce

/-- Dissipative equilibrium means the entropy force lies in the null space of `L`. -/
def IsDissipativeEquilibrium (F : MetriplecticFlow V) : Prop :=
  F.metric.onsager F.entropyForce = 0

/-- At dissipative equilibrium, the dissipative flow vanishes. -/
theorem dissipativeFlow_eq_zero_of_equilibrium
    (F : MetriplecticFlow V)
    (hEq : F.IsDissipativeEquilibrium) :
    F.dissipativeFlow = 0 := by
  rw [F.dissipativeFlow_eq_onsager_entropy, hEq]

/-- If the dissipative flow vanishes, the entropy force is in the null space of `L`. -/
theorem equilibrium_of_dissipativeFlow_eq_zero
    (F : MetriplecticFlow V)
    (hFlow : F.dissipativeFlow = 0) :
    F.IsDissipativeEquilibrium := by
  rw [IsDissipativeEquilibrium]
  rw [← F.dissipativeFlow_eq_onsager_entropy]
  exact hFlow

/-- Equilibrium is equivalent to vanishing dissipative flow. -/
theorem equilibrium_iff_dissipativeFlow_eq_zero
    (F : MetriplecticFlow V) :
    F.IsDissipativeEquilibrium ↔ F.dissipativeFlow = 0 :=
  ⟨F.dissipativeFlow_eq_zero_of_equilibrium,
    F.equilibrium_of_dissipativeFlow_eq_zero⟩

end MetriplecticFlow

/--
Scalar-body shadow of the coadjoint-leaf decomposition.

`leafEntropyChange` records the reversible/symplectic motion along a leaf,
while `transverseEntropyProduction` records the Onsager motion across leaves.
-/
structure CoadjointLeafEntropySplit where
  transverseEntropyProduction : ℝ
  totalEntropyChange : ℝ
  transverseEntropyProduction_nonnegative :
    0 ≤ transverseEntropyProduction
  totalEntropyChange_eq_transverse :
    totalEntropyChange = transverseEntropyProduction

namespace CoadjointLeafEntropySplit

/-- Transverse Onsager motion carries nonnegative entropy production. -/
theorem transverse_entropy_nonnegative (S : CoadjointLeafEntropySplit) :
    0 ≤ S.transverseEntropyProduction :=
  S.transverseEntropyProduction_nonnegative

/-- Total entropy change is nonnegative. -/
theorem totalEntropyChange_nonnegative
    (S : CoadjointLeafEntropySplit) :
    0 ≤ S.totalEntropyChange := by
  rw [S.totalEntropyChange_eq_transverse]
  exact S.transverseEntropyProduction_nonnegative

end CoadjointLeafEntropySplit

/--
Capstone packet for relativistic conformal viscous hydrodynamics at the
body-level abstraction used in this folder.

It combines:

* a metriplectic flow with energy degeneracy and nonnegative entropy production;
* a conformal `P/K` split into reversible and dissipative pieces;
* a perfect-CFT gate saying that zero trace/anomaly disables the conformal
  dissipative blocks.
-/
structure RelativisticConformalHydroCapstone
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  flow : MetriplecticFlow V
  pkSplit : ConformalPKMetriplecticSplit
  cftGate : PerfectCFTDissipationGate
  gate_LPK_matches_split :
    cftGate.LPKdiss = pkSplit.dissipativePK

namespace RelativisticConformalHydroCapstone

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
In the perfect-CFT limit (`conformalAnomaly = 0`), the dilation and conformal
cross dissipative channels vanish.
-/
theorem dissipative_conformal_blocks_vanish_of_anomaly_zero
    (C : RelativisticConformalHydroCapstone V)
    (hAnomaly : C.cftGate.conformalAnomaly = 0) :
    C.cftGate.LDD = 0 ∧ C.cftGate.LPD = 0 ∧ C.pkSplit.dissipativePK = 0 := by
  have hBlocks := C.cftGate.blocks_vanish_of_anomaly_zero hAnomaly
  rcases hBlocks with ⟨hDD, hPD, hPK⟩
  exact ⟨hDD, hPD, by
    rw [← C.gate_LPK_matches_split]
    exact hPK⟩

/--
The metriplectic second law remains nonnegative in the conformal hydrodynamic
capstone packet.
-/
theorem entropyProduction_nonnegative
    (C : RelativisticConformalHydroCapstone V) :
    0 ≤ C.flow.entropyProduction :=
  C.flow.entropyProduction_nonnegative

/-- The dissipative flow preserves energy by Onsager degeneracy. -/
theorem dissipative_energy_change_eq_zero
    (C : RelativisticConformalHydroCapstone V) :
    C.flow.metric.pairing C.flow.energyForce C.flow.dissipativeFlow = 0 :=
  C.flow.dissipative_energy_change_eq_zero

/--
Single capstone theorem:
zero conformal anomaly disables the conformal dissipative blocks while the
metriplectic flow retains energy degeneracy and nonnegative entropy production.
-/
theorem conformal_anomaly_zero_capstone
    (C : RelativisticConformalHydroCapstone V)
    (hAnomaly : C.cftGate.conformalAnomaly = 0) :
    C.cftGate.LDD = 0
      ∧ C.cftGate.LPD = 0
      ∧ C.pkSplit.dissipativePK = 0
      ∧ C.flow.metric.pairing C.flow.energyForce C.flow.dissipativeFlow = 0
      ∧ 0 ≤ C.flow.entropyProduction := by
  rcases C.dissipative_conformal_blocks_vanish_of_anomaly_zero hAnomaly with
    ⟨hDD, hPD, hPK⟩
  exact ⟨hDD, hPD, hPK,
    C.dissipative_energy_change_eq_zero,
    C.entropyProduction_nonnegative⟩

end RelativisticConformalHydroCapstone

end InfoGeometry.SuperMetriplectic
