import InfoGeometry.SuperMetriplectic.SeeleyDeWitt

/-!
# Information Equilibrium Theorem

Lean-only scalar/body-level formalization of the information-equilibrium
principle:

* the Moore-Penrose shell is the dissipative exterior;
* the Drazin core is the topological/protected interior;
* the stability index compares those two scalar readouts;
* near the BPS gate, entropy production vanishes in the protected lane;
* the Casimir/Weyl residual is exactly the informational cosmological
  constant keeping the Drazin core from collapse.

The theorem is intentionally proof-carrying.  It does not derive analytic
existence/uniqueness of a physical equilibrium from PDE or spectral analysis;
instead, those hypotheses are explicit fields.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Scalar stability index comparing Drazin topological core to Penrose dissipative
shell.

The division-free equation
`drazinCoreNorm = stabilityIndex * penroseShellNorm` is used so the packet does
not require invertibility of the shell norm.
-/
structure StabilityIndexPacket where
  drazinCoreNorm : ℝ
  penroseShellNorm : ℝ
  stabilityIndex : ℝ
  stabilityIndex_eq_ratio_shadow :
    drazinCoreNorm = stabilityIndex * penroseShellNorm
  bpsBalance :
    stabilityIndex = 1
  drazinCore_balances_penroseShell :
    drazinCoreNorm = penroseShellNorm

namespace StabilityIndexPacket

/-- Public division-free stability-index equation. -/
theorem drazin_eq_index_mul_penrose
    (S : StabilityIndexPacket) :
    S.drazinCoreNorm = S.stabilityIndex * S.penroseShellNorm :=
  S.stabilityIndex_eq_ratio_shadow

/-- In the BPS balance gate, the stability index is one. -/
theorem stabilityIndex_eq_one
    (S : StabilityIndexPacket) :
    S.stabilityIndex = 1 :=
  S.bpsBalance

/-- In the supplied BPS equilibrium gate, Drazin core balances Penrose shell. -/
theorem drazin_eq_penrose
    (S : StabilityIndexPacket) :
    S.drazinCoreNorm = S.penroseShellNorm :=
  S.drazinCore_balances_penroseShell

end StabilityIndexPacket

/--
Casimir residual as informational cosmological constant.

`collapseCounterterm` is the amount needed to stabilize the Drazin core against
the dissipative shell.  The packet identifies this counterterm with the
Casimir/Weyl residual and hence with `Λ_info`.
-/
structure InformationalCosmologicalConstantPacket where
  casimirResidual : ℝ
  lambdaInfo : ℝ
  collapseCounterterm : ℝ
  drazinCoreSupportEnergy : ℝ
  lambdaInfo_eq_casimirResidual :
    lambdaInfo = casimirResidual
  collapseCounterterm_eq_lambdaInfo :
    collapseCounterterm = lambdaInfo
  drazinCoreSupportEnergy_eq_lambdaInfo :
    drazinCoreSupportEnergy = lambdaInfo

namespace InformationalCosmologicalConstantPacket

/-- The informational cosmological constant is the Casimir residual. -/
theorem lambda_eq_casimirResidual
    (L : InformationalCosmologicalConstantPacket) :
    L.lambdaInfo = L.casimirResidual :=
  L.lambdaInfo_eq_casimirResidual

/-- The anti-collapse counterterm is the informational cosmological constant. -/
theorem collapseCounterterm_eq_lambda
    (L : InformationalCosmologicalConstantPacket) :
    L.collapseCounterterm = L.lambdaInfo :=
  L.collapseCounterterm_eq_lambdaInfo

/-- The Drazin support energy is the informational cosmological constant. -/
theorem drazinSupport_eq_lambda
    (L : InformationalCosmologicalConstantPacket) :
    L.drazinCoreSupportEnergy = L.lambdaInfo :=
  L.drazinCoreSupportEnergy_eq_lambdaInfo

/-- The anti-collapse counterterm is exactly the Casimir residual. -/
theorem collapseCounterterm_eq_casimirResidual
    (L : InformationalCosmologicalConstantPacket) :
    L.collapseCounterterm = L.casimirResidual := by
  rw [L.collapseCounterterm_eq_lambda, L.lambda_eq_casimirResidual]

end InformationalCosmologicalConstantPacket

/--
Equation-of-state equilibrium packet.

The conformal branch carries `w = 1/3` in division-free form `3P = ρ`; the BPS
branch carries the stiff/extremal balance `P = n`.
-/
structure InformationEquationOfStateEquilibrium where
  conformal : ConformalEquationOfStateLimit
  bps : BPSEquationOfStateLimit
  eosDeviation : ℝ
  eosDeviation_eq_bps_minus_conformal :
    eosDeviation = bps.pressureReadout - conformal.pressureReadout

namespace InformationEquationOfStateEquilibrium

/-- Conformal equation of state: `3P = ρ`. -/
theorem conformal_pressure_True
    (E : InformationEquationOfStateEquilibrium) :
    3 * E.conformal.pressureReadout = E.conformal.energyDensity :=
  E.conformal.pressure_True

/-- BPS/stiff equation of state: pressure balances charge density. -/
theorem bps_pressure_eq_charge
    (E : InformationEquationOfStateEquilibrium) :
    E.bps.pressureReadout = E.bps.chargeDensity :=
  E.bps.pressure_eq_charge

/-- EoS deviation readout between BPS and conformal pressure lanes. -/
theorem eosDeviation_eq
    (E : InformationEquationOfStateEquilibrium) :
    E.eosDeviation = E.bps.pressureReadout - E.conformal.pressureReadout :=
  E.eosDeviation_eq_bps_minus_conformal

end InformationEquationOfStateEquilibrium

/--
Abstract unique equilibrium witness.

`State` is left abstract because this scalar layer does not own the concrete
operator state space.
-/
structure UniqueInformationEquilibrium (State : Type*) where
  equilibriumState : State
  IsEquilibrium : State → Prop
  equilibrium_proof :
    IsEquilibrium equilibriumState
  unique_equilibrium :
    ∀ s, IsEquilibrium s → s = equilibriumState

namespace UniqueInformationEquilibrium

variable {State : Type*}

/-- The supplied equilibrium state satisfies the equilibrium predicate. -/
theorem equilibrium_holds
    (U : UniqueInformationEquilibrium State) :
    U.IsEquilibrium U.equilibriumState :=
  U.equilibrium_proof

/-- Any equilibrium state is the supplied equilibrium state. -/
theorem unique
    (U : UniqueInformationEquilibrium State)
    (s : State)
    (hs : U.IsEquilibrium s) :
    s = U.equilibriumState :=
  U.unique_equilibrium s hs

end UniqueInformationEquilibrium

/--
Full information-equilibrium capstone.
-/
structure InformationEquilibriumCapstone
    (ι : Type*) [Fintype ι] (State : Type*) where
  seeley : SeeleyDeWittCasimirCapstone ι
  stability : StabilityIndexPacket
  lambdaInfo : InformationalCosmologicalConstantPacket
  eos : InformationEquationOfStateEquilibrium
  uniqueEquilibrium : UniqueInformationEquilibrium State
  entropyProduction : ℝ
  entropyProduction_eq_zero :
    entropyProduction = 0
  lambdaInfo_matches_casimir :
    lambdaInfo.casimirResidual =
      seeley.casimirCapstone.casimir.weylAnomalyResidual
  lambdaInfo_matches_cosmologicalConstant :
    lambdaInfo.lambdaInfo =
      seeley.casimirCapstone.lambdaBridge.cosmologicalConstant

namespace InformationEquilibriumCapstone

variable {ι : Type*} [Fintype ι] {State : Type*}

/-- Equilibrium has zero entropy production in the protected/BPS gate. -/
theorem entropyProduction_zero
    (C : InformationEquilibriumCapstone ι State) :
    C.entropyProduction = 0 :=
  C.entropyProduction_eq_zero

/-- Stability index reaches the BPS value one. -/
theorem stabilityIndex_eq_one
    (C : InformationEquilibriumCapstone ι State) :
    C.stability.stabilityIndex = 1 :=
  C.stability.stabilityIndex_eq_one

/-- Drazin core balances the Penrose shell at equilibrium. -/
theorem drazinCore_eq_penroseShell
    (C : InformationEquilibriumCapstone ι State) :
    C.stability.drazinCoreNorm = C.stability.penroseShellNorm :=
  C.stability.drazin_eq_penrose

/-- Informational cosmological constant is the Weyl/Casimir residual. -/
theorem lambdaInfo_eq_weylResidual
    (C : InformationEquilibriumCapstone ι State) :
    C.lambdaInfo.lambdaInfo =
      C.seeley.casimirCapstone.casimir.weylAnomalyResidual := by
  rw [C.lambdaInfo.lambda_eq_casimirResidual, C.lambdaInfo_matches_casimir]

/-- Informational cosmological constant is the existing Casimir lambda bridge. -/
theorem lambdaInfo_eq_cosmologicalConstant
    (C : InformationEquilibriumCapstone ι State) :
    C.lambdaInfo.lambdaInfo =
      C.seeley.casimirCapstone.lambdaBridge.cosmologicalConstant :=
  C.lambdaInfo_matches_cosmologicalConstant

/-- The Drazin anti-collapse counterterm is the Weyl/Casimir residual. -/
theorem collapseCounterterm_eq_weylResidual
    (C : InformationEquilibriumCapstone ι State) :
    C.lambdaInfo.collapseCounterterm =
      C.seeley.casimirCapstone.casimir.weylAnomalyResidual := by
  rw [C.lambdaInfo.collapseCounterterm_eq_lambda,
    C.lambdaInfo_eq_weylResidual]

/-- The supplied equilibrium state is unique. -/
theorem unique_equilibrium
    (C : InformationEquilibriumCapstone ι State)
    (s : State)
    (hs : C.uniqueEquilibrium.IsEquilibrium s) :
    s = C.uniqueEquilibrium.equilibriumState :=
  C.uniqueEquilibrium.unique s hs

/--
Information Equilibrium Theorem:
zero entropy production, Drazin/Penrose balance, stability index one, BPS EoS,
and Casimir residual as informational cosmological constant / Drazin
anti-collapse support.
-/
theorem information_equilibrium_theorem
    (C : InformationEquilibriumCapstone ι State) :
    C.entropyProduction = 0
      ∧ C.stability.stabilityIndex = 1
      ∧ C.stability.drazinCoreNorm = C.stability.penroseShellNorm
      ∧ C.eos.bps.pressureReadout = C.eos.bps.chargeDensity
      ∧ C.lambdaInfo.lambdaInfo =
          C.seeley.casimirCapstone.casimir.weylAnomalyResidual
      ∧ C.lambdaInfo.collapseCounterterm =
          C.seeley.casimirCapstone.casimir.weylAnomalyResidual := by
  exact ⟨C.entropyProduction_zero,
    C.stabilityIndex_eq_one,
    C.drazinCore_eq_penroseShell,
    C.eos.bps_pressure_eq_charge,
    C.lambdaInfo_eq_weylResidual,
    C.collapseCounterterm_eq_weylResidual⟩

end InformationEquilibriumCapstone

end InfoGeometry.SuperMetriplectic
