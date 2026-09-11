import InfoGeometry.SuperMetriplectic.DarkEnergyMapping
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Critical Stiffness for Dark-Energy Dominance

Lean-only scalar/body-level packet for the "critical stiffness" layer.

The stiffness readout is the second Weyl-scale variation of the logarithmic
Pfaffian at the informational cosmological-constant gate.  The critical value
is the threshold at which the Drazin/Pfaffian support dominates the Penrose
collapse channel, producing the dark-energy fixed point.

No analytic second-variation theorem or numerical simulation is claimed here;
those are represented by explicit scalar fields.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Pfaffian stiffness readout.

The intended expression is
`κ = δ² log Pf / δσ² |_{σ = Λ}`.
-/
structure PfaffianStiffnessPacket where
  weylScaleAtLambda : ℝ
  secondVariationLogPfaffian : ℝ
  stiffness : ℝ
  stiffness_eq_secondVariation :
    stiffness = secondVariationLogPfaffian

namespace PfaffianStiffnessPacket

/-- Stiffness is the second Weyl variation of the logarithmic Pfaffian readout. -/
theorem stiffness_eq_secondVariationReadout
    (K : PfaffianStiffnessPacket) :
    K.stiffness = K.secondVariationLogPfaffian :=
  K.stiffness_eq_secondVariation

end PfaffianStiffnessPacket

/--
Critical stiffness threshold.

`criticalStiffness` is the exact value needed for the Drazin/Pfaffian support to
balance Penrose collapse at the dark-energy fixed point.
-/
structure CriticalStiffnessThreshold where
  stiffness : ℝ
  criticalStiffness : ℝ
  penroseCollapseModulus : ℝ
  drazinSupportModulus : ℝ
  criticalStiffness_eq_penroseCollapse :
    criticalStiffness = penroseCollapseModulus
  drazinSupport_eq_critical :
    drazinSupportModulus = criticalStiffness
  stiffness_reaches_critical :
    stiffness = criticalStiffness

namespace CriticalStiffnessThreshold

/-- Critical stiffness equals the Penrose collapse modulus. -/
theorem critical_eq_penroseCollapse
    (K : CriticalStiffnessThreshold) :
    K.criticalStiffness = K.penroseCollapseModulus :=
  K.criticalStiffness_eq_penroseCollapse

/-- Drazin support modulus reaches the critical stiffness. -/
theorem drazinSupport_eq_criticalStiffness
    (K : CriticalStiffnessThreshold) :
    K.drazinSupportModulus = K.criticalStiffness :=
  K.drazinSupport_eq_critical

/-- The system reaches the critical stiffness gate. -/
theorem stiffness_eq_critical
    (K : CriticalStiffnessThreshold) :
    K.stiffness = K.criticalStiffness :=
  K.stiffness_reaches_critical

/-- At the critical gate, Drazin support equals Penrose collapse. -/
theorem drazinSupport_eq_penroseCollapse
    (K : CriticalStiffnessThreshold) :
    K.drazinSupportModulus = K.penroseCollapseModulus := by
  rw [K.drazinSupport_eq_criticalStiffness, K.critical_eq_penroseCollapse]

end CriticalStiffnessThreshold

/--
Dark-energy dominance gate.

The dominance condition is recorded division-free as an equality at threshold:
`Λ_eff = Λ_crit`, with both sides tied to stiffness and Casimir residuals.
-/
structure DarkEnergyDominanceGate where
  lambdaEff : ℝ
  lambdaCritical : ℝ
  casimirResidual : ℝ
  criticalStiffness : ℝ
  lambdaEff_eq_casimirResidual :
    lambdaEff = casimirResidual
  lambdaCritical_eq_criticalStiffness :
    lambdaCritical = criticalStiffness
  lambdaEff_reaches_threshold :
    lambdaEff = lambdaCritical

namespace DarkEnergyDominanceGate

/-- Dark-energy dominance is the concrete threshold inequality. -/
def darkEnergyDominates (G : DarkEnergyDominanceGate) : Prop :=
  G.lambdaCritical ≤ G.lambdaEff

/-- Effective lambda is the Casimir residual. -/
theorem lambdaEff_eq_casimir
    (G : DarkEnergyDominanceGate) :
    G.lambdaEff = G.casimirResidual :=
  G.lambdaEff_eq_casimirResidual

/-- Critical lambda is the critical stiffness readout. -/
theorem lambdaCritical_eq_stiffness
    (G : DarkEnergyDominanceGate) :
    G.lambdaCritical = G.criticalStiffness :=
  G.lambdaCritical_eq_criticalStiffness

/-- At the supplied threshold, dark-energy dominance holds. -/
theorem dominance_holds
    (G : DarkEnergyDominanceGate) :
    G.darkEnergyDominates :=
  le_of_eq G.lambdaEff_reaches_threshold.symm

end DarkEnergyDominanceGate

/--
Effective Weyl-Casimir action readout.

The intended scalar shadow is
`S_eff(σ) = log Pf_reg(i𝓓_σ) - 1/2 log Ber_reg(M_σ)`.
This packet records the relation as an explicit body-level equality, without
claiming the analytic construction of the functional determinant.
-/
structure WeylCasimirEffectiveActionPacket where
  weylScale : ℝ
  effectiveAction : ℝ
  logPfaffian : ℝ
  logBerezinian : ℝ
  effectiveAction_eq :
    effectiveAction = logPfaffian - (1 / 2 : ℝ) * logBerezinian

namespace WeylCasimirEffectiveActionPacket

/-- Effective action is the Pfaffian contribution minus half the Berezinian contribution. -/
theorem effectiveAction_eq_pfaffian_sub_half_berezinian
    (A : WeylCasimirEffectiveActionPacket) :
    A.effectiveAction = A.logPfaffian - (1 / 2 : ℝ) * A.logBerezinian :=
  A.effectiveAction_eq

end WeylCasimirEffectiveActionPacket

/--
Analytic critical-density shadow for
`κ = α Z² - β G_info ρ_info`.

The critical density is recorded in multiplication form:
`(β G_info) ρcrit = α Z²`.  This avoids hiding the nonzero-denominator
condition that would be needed to rewrite it as
`ρcrit = α/(β G_info) Z²`.
-/
structure CasimirWeylCriticalDensityPacket where
  alphaD4 : ℝ
  betaD4 : ℝ
  infoNewton : ℝ
  centralCharge : ℝ
  localInfoDensity : ℝ
  criticalInfoDensity : ℝ
  stiffness : ℝ
  stiffness_eq :
    stiffness =
      alphaD4 * centralCharge ^ 2
        - (betaD4 * infoNewton) * localInfoDensity
  criticalDensity_balance :
    (betaD4 * infoNewton) * criticalInfoDensity =
      alphaD4 * centralCharge ^ 2

namespace CasimirWeylCriticalDensityPacket

/-- The supplied stiffness readout has the Casimir-Weyl form `αZ² - βGρ`. -/
theorem stiffness_eq_alphaZ_sq_sub_betaG_rho
    (K : CasimirWeylCriticalDensityPacket) :
    K.stiffness =
      K.alphaD4 * K.centralCharge ^ 2
        - (K.betaD4 * K.infoNewton) * K.localInfoDensity :=
  K.stiffness_eq

/-- Division-free critical-density equation: `(βG)ρcrit = αZ²`. -/
theorem criticalDensity_mul_betaG_eq_alphaZ_sq
    (K : CasimirWeylCriticalDensityPacket) :
    (K.betaD4 * K.infoNewton) * K.criticalInfoDensity =
      K.alphaD4 * K.centralCharge ^ 2 :=
  K.criticalDensity_balance

/-- At the critical information density, the stiffness is zero. -/
theorem stiffness_eq_zero_at_criticalDensity
    (K : CasimirWeylCriticalDensityPacket) :
    K.localInfoDensity = K.criticalInfoDensity →
    K.stiffness = 0 := by
  intro hρ
  rw [K.stiffness_eq_alphaZ_sq_sub_betaG_rho, hρ]
  rw [← K.criticalDensity_mul_betaG_eq_alphaZ_sq]
  ring

/--
Below the critical density, the Drazin/Casimir term dominates and the
stiffness is strictly positive, provided the effective coupling `βG` is
positive.
-/
theorem stiffness_pos_of_localDensity_lt_critical
    (K : CasimirWeylCriticalDensityPacket)
    (hβG : 0 < K.betaD4 * K.infoNewton)
    (hρ : K.localInfoDensity < K.criticalInfoDensity) :
    0 < K.stiffness := by
  rw [K.stiffness_eq_alphaZ_sq_sub_betaG_rho]
  rw [← K.criticalDensity_mul_betaG_eq_alphaZ_sq]
  have hdiff : 0 < K.criticalInfoDensity - K.localInfoDensity :=
    sub_pos.mpr hρ
  have hprod :
      0 < (K.betaD4 * K.infoNewton)
        * (K.criticalInfoDensity - K.localInfoDensity) :=
    mul_pos hβG hdiff
  nlinarith

/--
Above the critical density, the Penrose collapse channel dominates and the
stiffness is strictly negative, provided the effective coupling `βG` is
positive.
-/
theorem stiffness_neg_of_critical_lt_localDensity
    (K : CasimirWeylCriticalDensityPacket)
    (hβG : 0 < K.betaD4 * K.infoNewton)
    (hρ : K.criticalInfoDensity < K.localInfoDensity) :
    K.stiffness < 0 := by
  rw [K.stiffness_eq_alphaZ_sq_sub_betaG_rho]
  rw [← K.criticalDensity_mul_betaG_eq_alphaZ_sq]
  have hdiff : K.criticalInfoDensity - K.localInfoDensity < 0 :=
    sub_neg.mpr hρ
  have hprod :
      (K.betaD4 * K.infoNewton)
        * (K.criticalInfoDensity - K.localInfoDensity) < 0 :=
    mul_neg_of_pos_of_neg hβG hdiff
  nlinarith

end CasimirWeylCriticalDensityPacket

/--
Dark-energy ignition packet.

The informal condition "when the Penrose-shell density drops below the
critical density, the Drazin/Casimir term dominates" is represented as an
explicit implication over a scalar threshold predicate.
-/
structure DarkEnergyIgnitionPacket where
  localInfoDensity : ℝ
  criticalInfoDensity : ℝ
  belowCritical :
    localInfoDensity ≤ criticalInfoDensity

namespace DarkEnergyIgnitionPacket

/-- Ignition dominance is exactly the below-critical density inequality. -/
def darkEnergyDominates (I : DarkEnergyIgnitionPacket) : Prop :=
  I.localInfoDensity ≤ I.criticalInfoDensity

/-- Below the critical density, the supplied packet enters dark-energy dominance. -/
theorem darkEnergyDominates_of_belowCritical
    (I : DarkEnergyIgnitionPacket) :
    I.darkEnergyDominates :=
  I.belowCritical

end DarkEnergyIgnitionPacket

/--
Critical-stiffness capstone over the dark-energy mapping.
-/
structure CriticalStiffnessCapstone
    (ι : Type*) [Fintype ι] (State : Type*) where
  darkEnergy : DarkEnergyMappingCapstone ι State
  pfaffianStiffness : PfaffianStiffnessPacket
  threshold : CriticalStiffnessThreshold
  dominance : DarkEnergyDominanceGate
  stiffness_matches_threshold :
    pfaffianStiffness.stiffness = threshold.stiffness
  dominance_lambda_matches_darkEnergy :
    dominance.lambdaEff = darkEnergy.darkEnergy.darkEnergyReadout
  dominance_casimir_matches_weylResidual :
    dominance.casimirResidual =
      darkEnergy.equilibrium.seeley.casimirCapstone.casimir.weylAnomalyResidual

namespace CriticalStiffnessCapstone

variable {ι : Type*} [Fintype ι] {State : Type*}

/-- Pfaffian stiffness reaches the critical threshold. -/
theorem pfaffianStiffness_eq_critical
    (C : CriticalStiffnessCapstone ι State) :
    C.pfaffianStiffness.stiffness = C.threshold.criticalStiffness := by
  rw [C.stiffness_matches_threshold]
  exact C.threshold.stiffness_eq_critical

/-- Critical Drazin support balances Penrose collapse. -/
theorem drazinSupport_eq_penroseCollapse
    (C : CriticalStiffnessCapstone ι State) :
    C.threshold.drazinSupportModulus = C.threshold.penroseCollapseModulus :=
  C.threshold.drazinSupport_eq_penroseCollapse

/-- Dark-energy dominance holds at the supplied critical gate. -/
theorem darkEnergyDominates
    (C : CriticalStiffnessCapstone ι State) :
    C.dominance.darkEnergyDominates :=
  C.dominance.dominance_holds

/-- The dominance lambda is the dark-energy readout. -/
theorem dominanceLambda_eq_darkEnergy
    (C : CriticalStiffnessCapstone ι State) :
    C.dominance.lambdaEff = C.darkEnergy.darkEnergy.darkEnergyReadout :=
  C.dominance_lambda_matches_darkEnergy

/--
Critical Stiffness Theorem:
the Pfaffian second-variation stiffness reaches the critical threshold,
Drazin support balances Penrose collapse, and dark-energy dominance holds.
-/
theorem critical_stiffness_theorem
    (C : CriticalStiffnessCapstone ι State) :
    C.pfaffianStiffness.stiffness = C.threshold.criticalStiffness
      ∧ C.threshold.drazinSupportModulus = C.threshold.penroseCollapseModulus
      ∧ C.dominance.lambdaEff = C.darkEnergy.darkEnergy.darkEnergyReadout
      ∧ C.dominance.darkEnergyDominates := by
  exact ⟨C.pfaffianStiffness_eq_critical,
    C.drazinSupport_eq_penroseCollapse,
    C.dominanceLambda_eq_darkEnergy,
    C.darkEnergyDominates⟩

end CriticalStiffnessCapstone

/--
Capstone for the analytic critical-density form of the same threshold.
-/
structure CasimirWeylCriticalDensityCapstone
    (ι : Type*) [Fintype ι] (State : Type*) where
  critical : CriticalStiffnessCapstone ι State
  effectiveAction : WeylCasimirEffectiveActionPacket
  density : CasimirWeylCriticalDensityPacket
  ignition : DarkEnergyIgnitionPacket
  density_stiffness_matches_threshold :
    density.stiffness = critical.threshold.criticalStiffness
  ignition_density_matches :
    ignition.localInfoDensity = density.localInfoDensity
      ∧ ignition.criticalInfoDensity = density.criticalInfoDensity
  localDensity_eq_critical :
    density.localInfoDensity = density.criticalInfoDensity

namespace CasimirWeylCriticalDensityCapstone

variable {ι : Type*} [Fintype ι] {State : Type*}

/-- The critical-density formula places the system at zero stiffness. -/
theorem density_stiffness_zero
    (C : CasimirWeylCriticalDensityCapstone ι State) :
    C.density.stiffness = 0 :=
  C.density.stiffness_eq_zero_at_criticalDensity C.localDensity_eq_critical

/-- Therefore the critical threshold readout is zero in this balanced packet. -/
theorem criticalStiffness_eq_zero
    (C : CasimirWeylCriticalDensityCapstone ι State) :
    C.critical.threshold.criticalStiffness = 0 := by
  rw [← C.density_stiffness_matches_threshold]
  exact C.density_stiffness_zero

/-- The ignition predicate supplied by the below-critical gate holds. -/
theorem darkEnergyDominates_from_densityGate
    (C : CasimirWeylCriticalDensityCapstone ι State) :
    C.ignition.darkEnergyDominates :=
  C.ignition.darkEnergyDominates_of_belowCritical

/--
Casimir-Weyl critical-density theorem:
the effective action has the Pfaffian/Berezinian split, the critical density
obeys `(βG)ρcrit = αZ²`, the stiffness vanishes at the critical point, and the
below-critical ignition gate yields dark-energy dominance.
-/
theorem casimir_weyl_critical_density_theorem
    (C : CasimirWeylCriticalDensityCapstone ι State) :
    C.effectiveAction.effectiveAction =
        C.effectiveAction.logPfaffian
          - (1 / 2 : ℝ) * C.effectiveAction.logBerezinian
      ∧ (C.density.betaD4 * C.density.infoNewton)
          * C.density.criticalInfoDensity =
            C.density.alphaD4 * C.density.centralCharge ^ 2
      ∧ C.density.stiffness = 0
      ∧ C.critical.threshold.criticalStiffness = 0
      ∧ C.ignition.darkEnergyDominates := by
  exact ⟨C.effectiveAction.effectiveAction_eq_pfaffian_sub_half_berezinian,
    C.density.criticalDensity_mul_betaG_eq_alphaZ_sq,
    C.density_stiffness_zero,
    C.criticalStiffness_eq_zero,
    C.darkEnergyDominates_from_densityGate⟩

end CasimirWeylCriticalDensityCapstone

/--
Below-critical phase capstone.

This is separate from the critical-gate capstone: here
`ρ_info < ρcrit`, so the stiffness is strictly positive when the effective
coupling `βG` is positive.
-/
structure CasimirWeylBelowCriticalPhaseCapstone where
  density : CasimirWeylCriticalDensityPacket
  ignition : DarkEnergyIgnitionPacket
  betaG_pos :
    0 < density.betaD4 * density.infoNewton
  strict_below_critical :
    density.localInfoDensity < density.criticalInfoDensity
  ignition_density_matches :
    ignition.localInfoDensity = density.localInfoDensity
      ∧ ignition.criticalInfoDensity = density.criticalInfoDensity

namespace CasimirWeylBelowCriticalPhaseCapstone

/-- In the below-critical phase, the stiffness is strictly positive. -/
theorem stiffness_pos
    (C : CasimirWeylBelowCriticalPhaseCapstone) :
    0 < C.density.stiffness :=
  C.density.stiffness_pos_of_localDensity_lt_critical
    C.betaG_pos C.strict_below_critical

/-- The supplied below-critical phase implies dark-energy dominance. -/
theorem darkEnergyDominates
    (C : CasimirWeylBelowCriticalPhaseCapstone) :
    C.ignition.darkEnergyDominates :=
  C.ignition.darkEnergyDominates_of_belowCritical

/--
Below-critical ignition theorem:
`ρ_info < ρcrit` with positive `βG` gives `κ > 0`, and the supplied dominance
gate enters the dark-energy phase.
-/
theorem below_critical_ignition_theorem
    (C : CasimirWeylBelowCriticalPhaseCapstone) :
    0 < C.density.stiffness
      ∧ C.ignition.darkEnergyDominates := by
  exact ⟨C.stiffness_pos, C.darkEnergyDominates⟩

end CasimirWeylBelowCriticalPhaseCapstone

end InfoGeometry.SuperMetriplectic
