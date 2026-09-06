import InfoGeometry.SuperMetriplectic.SupervolumeFunctional

/-!
# Casimir Energy from Zeta/Supervolume Residues

Lean-only scalar/body-level packet for the Casimir-energy layer of the
supervolume model.

The file records the stable algebraic interfaces:

* Casimir energy as the negative beta-derivative of the regularized Berezinian;
* zeta-zero sector signs for bosonic and Majorana/fermionic lanes;
* BPS cancellation leaving a central-charge residual;
* the Casimir readout as a cosmological-constant/Fisher-curvature source;
* Pfaffian topological index as regulator of the Casimir flow.

No analytic zeta continuation, heat-kernel expansion, or concrete spectral
calculation is claimed here.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Signed zeta-zero sector packet.

`totalZetaZero` is the signed body readout: bosonic contribution minus
fermionic/Majorana contribution plus a topological residual.
-/
structure ZetaZeroSectorPacket where
  bosonicZetaZero : ℝ
  fermionicZetaZero : ℝ
  topologicalResidual : ℝ
  totalZetaZero : ℝ
  totalZetaZero_eq :
    totalZetaZero = bosonicZetaZero - fermionicZetaZero + topologicalResidual

namespace ZetaZeroSectorPacket

/-- Public signed `ζ(0)` sector decomposition. -/
theorem total_eq
    (Z : ZetaZeroSectorPacket) :
    Z.totalZetaZero =
      Z.bosonicZetaZero - Z.fermionicZetaZero + Z.topologicalResidual :=
  Z.totalZetaZero_eq

end ZetaZeroSectorPacket

/--
Casimir energy packet from the regularized Berezinian.

The intended expression is
`E_C = lim_{β → ∞} -∂_β log Ber_reg(M)`.
This layer stores the limiting derivative readout as a scalar field.
-/
structure CasimirEnergyPacket where
  betaDerivativeLogBerezinianAtInfinity : ℝ
  casimirEnergy : ℝ
  weylAnomalyResidual : ℝ
  zetaZero : ZetaZeroSectorPacket
  casimirEnergy_eq_neg_betaDerivative :
    casimirEnergy = -betaDerivativeLogBerezinianAtInfinity
  casimirEnergy_eq_weylAnomalyResidual :
    casimirEnergy = weylAnomalyResidual

namespace CasimirEnergyPacket

/-- Casimir energy is the negative beta-derivative of log Berezinian at infinity. -/
theorem casimirEnergy_eq_neg_derivative
    (C : CasimirEnergyPacket) :
    C.casimirEnergy = -C.betaDerivativeLogBerezinianAtInfinity :=
  C.casimirEnergy_eq_neg_betaDerivative

/-- Casimir energy is the Weyl-anomaly residual in this packet. -/
theorem casimirEnergy_eq_anomaly
    (C : CasimirEnergyPacket) :
    C.casimirEnergy = C.weylAnomalyResidual :=
  C.casimirEnergy_eq_weylAnomalyResidual

end CasimirEnergyPacket

/--
`D₄` Casimir density packet.

The density is the signed half-sum of bosonic and fermionic spectral weights,
plus a topological residual.
-/
structure D4CasimirDensityPacket where
  bosonicWeightSum : ℝ
  fermionicWeightSum : ℝ
  topologicalResidual : ℝ
  casimirDensity : ℝ
  casimirDensity_eq :
    casimirDensity =
      (1 / 2 : ℝ) * (bosonicWeightSum - fermionicWeightSum)
        + topologicalResidual

namespace D4CasimirDensityPacket

/-- Public `D₄` signed Casimir density readout. -/
theorem density_eq
    (D : D4CasimirDensityPacket) :
    D.casimirDensity =
      (1 / 2 : ℝ) * (D.bosonicWeightSum - D.fermionicWeightSum)
        + D.topologicalResidual :=
  D.casimirDensity_eq

end D4CasimirDensityPacket

/--
BPS cancellation packet.

The signed vacuum pressure is the bosonic outward contribution minus the
fermionic attractive contribution.  In the protected limit it leaves only the
central-charge residual.
-/
structure BPSCasimirCancellationPacket where
  bosonicOutwardPressure : ℝ
  fermionicAttraction : ℝ
  signedVacuumPressure : ℝ
  centralChargeResidual : ℝ
  signedVacuumPressure_eq :
    signedVacuumPressure = bosonicOutwardPressure - fermionicAttraction
  bpsCancellation_eq_central :
    signedVacuumPressure = centralChargeResidual

namespace BPSCasimirCancellationPacket

/-- Signed pressure is bosonic outward pressure minus fermionic attraction. -/
theorem signedVacuumPressure_eq_diff
    (B : BPSCasimirCancellationPacket) :
    B.signedVacuumPressure = B.bosonicOutwardPressure - B.fermionicAttraction :=
  B.signedVacuumPressure_eq

/-- BPS cancellation leaves the central-charge residual. -/
theorem signedVacuumPressure_eq_central
    (B : BPSCasimirCancellationPacket) :
    B.signedVacuumPressure = B.centralChargeResidual :=
  B.bpsCancellation_eq_central

end BPSCasimirCancellationPacket

/--
Casimir/cosmological-constant bridge.

The Casimir readout is treated as the vacuum source for the Fisher curvature
lane, i.e. the scalar cosmological-constant shadow.
-/
structure CasimirCosmologicalConstantBridge where
  casimir : CasimirEnergyPacket
  cosmologicalConstant : ℝ
  fisherCurvatureSource : ℝ
  cosmologicalConstant_eq_casimir :
    cosmologicalConstant = casimir.casimirEnergy
  fisherCurvatureSource_eq_lambda :
    fisherCurvatureSource = cosmologicalConstant

namespace CasimirCosmologicalConstantBridge

/-- The cosmological-constant readout is the Casimir energy. -/
theorem lambda_eq_casimir
    (B : CasimirCosmologicalConstantBridge) :
    B.cosmologicalConstant = B.casimir.casimirEnergy :=
  B.cosmologicalConstant_eq_casimir

/-- Fisher curvature source is the cosmological-constant readout. -/
theorem fisherSource_eq_lambda
    (B : CasimirCosmologicalConstantBridge) :
    B.fisherCurvatureSource = B.cosmologicalConstant :=
  B.fisherCurvatureSource_eq_lambda

/-- Fisher curvature source directly reads the Casimir energy. -/
theorem fisherSource_eq_casimir
    (B : CasimirCosmologicalConstantBridge) :
    B.fisherCurvatureSource = B.casimir.casimirEnergy := by
  rw [B.fisherSource_eq_lambda, B.lambda_eq_casimir]

end CasimirCosmologicalConstantBridge

/--
Pfaffian topological-index regulator for the Casimir flow.
-/
structure PfaffianCasimirFlowRegulator where
  pfaffianIndex : ℝ
  centralCharge : ℝ
  rawCasimirFlow : ℝ
  regulatedCasimirFlow : ℝ
  regulatedCasimirFlow_eq :
    regulatedCasimirFlow = rawCasimirFlow + pfaffianIndex * centralCharge

namespace PfaffianCasimirFlowRegulator

/-- Public regulated Casimir-flow equation. -/
theorem regulatedFlow_eq
    (R : PfaffianCasimirFlowRegulator) :
    R.regulatedCasimirFlow = R.rawCasimirFlow + R.pfaffianIndex * R.centralCharge :=
  R.regulatedCasimirFlow_eq

end PfaffianCasimirFlowRegulator

/--
Final Casimir-zeta capstone over the supervolume functional.
-/
structure SupervolumeCasimirZetaCapstone (ι : Type*) [Fintype ι] where
  supervolume : InformationSuperGasSupervolumeCapstone ι
  casimir : CasimirEnergyPacket
  density : D4CasimirDensityPacket
  bpsCancellation : BPSCasimirCancellationPacket
  lambdaBridge : CasimirCosmologicalConstantBridge
  pfaffianRegulator : PfaffianCasimirFlowRegulator
  lambdaBridge_uses_casimir :
    lambdaBridge.casimir = casimir

namespace SupervolumeCasimirZetaCapstone

variable {ι : Type*} [Fintype ι]

/-- Casimir energy is the Weyl-anomaly residual. -/
theorem casimir_eq_anomaly
    (C : SupervolumeCasimirZetaCapstone ι) :
    C.casimir.casimirEnergy = C.casimir.weylAnomalyResidual :=
  C.casimir.casimirEnergy_eq_anomaly

/-- BPS Casimir cancellation leaves the central-charge residual. -/
theorem bps_pressure_eq_central
    (C : SupervolumeCasimirZetaCapstone ι) :
    C.bpsCancellation.signedVacuumPressure =
      C.bpsCancellation.centralChargeResidual :=
  C.bpsCancellation.signedVacuumPressure_eq_central

/-- The cosmological-constant readout is the Casimir energy. -/
theorem lambda_eq_casimir
    (C : SupervolumeCasimirZetaCapstone ι) :
    C.lambdaBridge.cosmologicalConstant = C.casimir.casimirEnergy := by
  rw [← C.lambdaBridge_uses_casimir]
  exact C.lambdaBridge.lambda_eq_casimir

/-- The Pfaffian index regulates the Casimir flow. -/
theorem regulatedFlow_eq
    (C : SupervolumeCasimirZetaCapstone ι) :
    C.pfaffianRegulator.regulatedCasimirFlow =
      C.pfaffianRegulator.rawCasimirFlow
        + C.pfaffianRegulator.pfaffianIndex
          * C.pfaffianRegulator.centralCharge :=
  C.pfaffianRegulator.regulatedFlow_eq

/--
Final zeta/Casimir theorem:
Casimir energy is a Weyl-anomaly residual, the `D₄` density is signed
boson-minus-fermion plus topology, BPS cancellation leaves the central charge,
the cosmological constant reads the Casimir energy, and the Pfaffian index
regulates the Casimir flow.
-/
theorem casimir_zeta_capstone
    (C : SupervolumeCasimirZetaCapstone ι) :
    C.casimir.casimirEnergy = C.casimir.weylAnomalyResidual
      ∧ C.density.casimirDensity =
          (1 / 2 : ℝ) * (C.density.bosonicWeightSum - C.density.fermionicWeightSum)
            + C.density.topologicalResidual
      ∧ C.bpsCancellation.signedVacuumPressure =
          C.bpsCancellation.centralChargeResidual
      ∧ C.lambdaBridge.cosmologicalConstant = C.casimir.casimirEnergy
      ∧ C.pfaffianRegulator.regulatedCasimirFlow =
          C.pfaffianRegulator.rawCasimirFlow
            + C.pfaffianRegulator.pfaffianIndex
              * C.pfaffianRegulator.centralCharge := by
  exact ⟨C.casimir_eq_anomaly,
    C.density.density_eq,
    C.bps_pressure_eq_central,
    C.lambda_eq_casimir,
    C.regulatedFlow_eq⟩

end SupervolumeCasimirZetaCapstone

end InfoGeometry.SuperMetriplectic
