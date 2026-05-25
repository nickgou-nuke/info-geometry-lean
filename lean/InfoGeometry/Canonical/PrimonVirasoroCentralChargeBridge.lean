import Mathlib
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Arithmetic.ArithmeticKMS
import InfoGeometry.Arithmetic.ZetaTraceVielbeinSpecialization
import InfoGeometry.Canonical.MassieuPlanckWeylScalarBridge
import InfoGeometry.Canonical.PrimeGasSuperKMSBridge
import InfoGeometry.Canonical.PrimeVirasoroSugawara
import InfoGeometry.Canonical.OperatorialCentralCharge
import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Krein.Clifford

/-!
# InfoGeometry.Canonical.PrimonVirasoroCentralChargeBridge

Theorem-safe bridge between the finite arithmetic primon KMS lane, the
prime zeta/Mellin lane, and the Virasoro / operatorial central-charge lane.

This file does not prove a prime-to-Virasoro theorem from scratch.  It packages
the exact compatibility data already supported by the repository:

* finite arithmetic KMS support and temperature readout;
* prime super-KMS temperature normalization;
* Massieu / Weyl scalar calibration;
* prime zeta-trace / Mellin readout;
* prime Sugawara/Virasoro central-charge calibration;
* topological central charge as the operatorial analytical index.

Any stronger arithmetic-to-conformal identity must be supplied by a separate
analytic owner surface.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimonVirasoroCentralCharge

open InfoGeometry.Arithmetic
open InfoGeometry.Arithmetic.ArithmeticKMS
open InfoGeometry.Canonical
open InfoGeometry.Canonical.MassieuPlanckWeylScalarBridge
open InfoGeometry.Canonical.PrimeGasSuperKMSBridge
open InfoGeometry.Canonical.PrimeVirasoroSugawara
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
open InfoGeometry.Krein
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle

/--
Prime-to-Virasoro compatibility packet.

`ArithmeticKMSWitness` carries the finite primon gas support and Gibbs flow.
`PrimeGasSuperKMSBridge` carries the even/odd supertemperature split.
`MassieuPlanckWeylScalarCalibration` carries the Souriau/Massieu scalar lane.
`PrimeVielbeinCarrier` carries the zeta-trace prime volume lane.
`PrimeSugawaraVirasoroPacket` carries the prime Sugawara/Virasoro lane.
`TopologicalCentralChargePackage` carries the operatorial central charge lane.

The bridge itself only stores the calibration equalities between those lanes.
-/
@[rep_depth thermo]
structure PrimonVirasoroCentralChargeBridge
    (State LieAlg Obs PrimeLabel Field Coeff Finite Alg A B E : Type)
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [KreinSpace (DoubledSpace E)]
    [KreinGradedModule (DoubledSpace E)] where
  /-- Finite arithmetic KMS owner. -/
  arithmetic : ArithmeticKMSWitness State

  /-- Finite support used for the arithmetic Gibbs readout. -/
  support : Finset ℕ

  /-- Finite inverse-temperature readout used on the arithmetic support. -/
  beta : ℝ

  /-- Finite arithmetic Gibbs partition readout. -/
  arithmeticPartition : ℝ

  /-- The arithmetic partition is the calibrated Gibbs flow readout. -/
  arithmeticPartition_eq :
    arithmeticPartition =
      arithmetic.modularFlowReadout (arithmetic.stateOfFinset support) beta

  /-- Prime super-KMS bridge carrying the even/odd temperature split. -/
  primeGas : PrimeGasSuperKMSBridge

  /-- Massieu/Weyl scalar calibration for the same thermal lane. -/
  massieu :
    MassieuPlanckWeylScalarCalibration
      (State := State) (LieAlgebra := LieAlg) (Obs := Obs)

  /-- The Massieu temperature is calibrated to the finite arithmetic inverse temperature. -/
  massieuBeta_eq :
    massieu.u = beta

  /--
  The calibrated Weyl scalar is identified with the finite arithmetic
  partition readout.
  -/
  massieuWeylScalar_eq_arithmeticPartition :
    massieu.weylScalar = arithmeticPartition

  /-- Canonical prime zeta-trace carrier. -/
  primeVielbein : PrimeVielbeinCarrier

  /-- The prime zeta-trace carrier is the canonical one already owned by the repo. -/
  primeVielbein_eq_canonical :
    primeVielbein = canonicalPrimeVielbein

  /-- The prime zeta-trace parameter. -/
  zetaParameter : ℂ

  /-- The zeta-trace parameter lies in the standard half-plane. -/
  zetaParameter_re_gt_one :
    1 < zetaParameter.re

  /-- Prime Sugawara/Virasoro owner packet. -/
  primeVirasoro :
    PrimeSugawaraVirasoroPacket PrimeLabel Field Coeff Finite Alg

  /-- Topological central-charge owner input. -/
  topologicalChargeX :
    InfoGeometry.KK.RealSplitKreinDiracFredholmModule A B (InfoGeometry.Krein.DoubledSpace E)

  /-- Topological central-charge chiral surface input. -/
  topologicalChargehX :
    InfoGeometry.KK.RealSplitKreinKasparovCycle.ChiralFredholmSurface topologicalChargeX

  /-- Operatorial central charge readout, stored as a model calibration. -/
  operatorialCharge : ℤ

  /-- The stored operatorial charge matches the operatorial analytic index. -/
  operatorialCharge_eq :
    operatorialCharge =
      operatorialCentralCharge
        (A := A) (B := B) (E := E) topologicalChargeX topologicalChargehX

  /-- Virasoro central-charge readout, stored as a model calibration. -/
  virasoroCentralCharge : ℝ

  /-- The stored Virasoro charge matches the Sugawara owner value. -/
  virasoroCentralCharge_eq :
    virasoroCentralCharge = primeVirasoro.affineVirasoro.centralCharge

  /-- Bridge-law guardrail: this packet is not a zero-location theorem. -/
  no_unconditional_zero_claim_guard : Type

namespace Bridge

variable
    {State LieAlg Obs PrimeLabel Field Coeff Finite Alg A B E : Type}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    [NormedRing A] [NormedRing B]
    [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [KreinSpace (DoubledSpace E)]
    [KreinGradedModule (DoubledSpace E)]

variable (P : PrimonVirasoroCentralChargeBridge
  State LieAlg Obs PrimeLabel Field Coeff Finite Alg A B E)

/-- The finite arithmetic partition is the calibrated Gibbs readout. -/
@[rep_depth thermo]
theorem arithmeticPartition_eq_gibbsReadout :
    P.arithmeticPartition =
      P.arithmetic.modularFlowReadout
        (P.arithmetic.stateOfFinset P.support) P.beta :=
  P.arithmeticPartition_eq

/-- The Massieu temperature equals the arithmetic inverse-temperature readout. -/
@[rep_depth thermo]
theorem massieuBeta_eq :
    P.massieu.u = P.beta :=
  P.massieuBeta_eq

/-- The calibrated Weyl scalar is the finite arithmetic partition readout. -/
@[rep_depth thermo]
theorem massieuWeylScalar_eq_arithmeticPartition :
    P.massieu.weylScalar = P.arithmeticPartition :=
  P.massieuWeylScalar_eq_arithmeticPartition

/-- The Massieu potential is the logarithm of the finite arithmetic partition. -/
@[rep_depth thermo]
theorem partitionPotential_eq_log_arithmeticPartition :
    P.massieu.souriau.partitionPotential = Real.log P.arithmeticPartition := by
  calc
    P.massieu.souriau.partitionPotential = Real.log P.massieu.weylScalar :=
      P.massieu.partitionPotential_eq_log_weylScalar
    _ = Real.log P.arithmeticPartition := by rw [P.massieuWeylScalar_eq_arithmeticPartition]

/-- The prime gas packet has vanishing odd supertemperature. -/
@[rep_depth thermo]
theorem primeGas_oddTemperature_eq_zero :
    P.primeGas.superTemperature.oddTemperature = 0 :=
  P.primeGas.superTemperature_odd_eq_zero

/-- The prime zeta-trace carrier is the canonical one from the repository. -/
@[rep_depth thermo]
theorem primeVielbein_eq_canonical :
    P.primeVielbein = canonicalPrimeVielbein :=
  P.primeVielbein_eq_canonical

/-- The prime trace-log supervolume equals the Riemann zeta function on the standard half-plane. -/
@[rep_depth thermo]
theorem primeTraceLogSupervolume_eq_riemannZeta :
    let V : PrimeVielbeinCarrier := P.primeVielbein
    InfoGeometry.Arithmetic.PrimeVielbeinCarrier.traceLogSupervolume V P.zetaParameter =
      riemannZeta P.zetaParameter := by
  dsimp
  rw [P.primeVielbein_eq_canonical]
  simpa [InfoGeometry.Arithmetic.PrimeVielbeinCarrier.traceLogSupervolume] using
    canonicalPrimeVielbein_traceLogSupervolume_eq_riemannZeta
      (s := P.zetaParameter) P.zetaParameter_re_gt_one

/-- The operatorial charge is exactly the topological central charge readout. -/
@[rep_depth krein]
theorem operatorialCharge_eq_analyticIndex :
    P.operatorialCharge = operatorialCentralCharge
      (A := A) (B := B) (E := E) P.topologicalChargeX P.topologicalChargehX := by
  exact P.operatorialCharge_eq

/-- The Virasoro central charge is exactly the Sugawara owner value. -/
@[rep_depth operator]
theorem virasoroCentralCharge_eq_sugawara :
    P.virasoroCentralCharge = P.primeVirasoro.affineVirasoro.centralCharge :=
  P.virasoroCentralCharge_eq

/-- Bridge re-export of the finite Sugawara cardinality specialization. -/
@[bridge_target_tag, rep_depth operator]
theorem primeVirasoroCentralCharge_eq_card_of_level_one_dualCoxeter_zero
    (S : Finset PrimeLabel)
    (hlevel : P.primeVirasoro.affineVirasoro.level = 1)
    (hdim : P.primeVirasoro.affineVirasoro.finiteDimension = (S.card : ℝ))
    (hdual : P.primeVirasoro.affineVirasoro.dualCoxeterNumber = 0)
    (hcc : P.primeVirasoro.affineVirasoro.centralCharge =
      P.primeVirasoro.affineVirasoro.level * P.primeVirasoro.affineVirasoro.finiteDimension /
        (P.primeVirasoro.affineVirasoro.level + P.primeVirasoro.affineVirasoro.dualCoxeterNumber)) :
    P.primeVirasoro.affineVirasoro.centralCharge = (S.card : ℝ) :=
  PrimeVirasoroSugawara.centralCharge_eq_card_of_level_one_dualCoxeter_zero
    P.primeVirasoro S hlevel hdim hdual hcc

/-- The Virasoro central charge is calibrated by the Sugawara owner theorem. -/
@[rep_depth operator]
theorem virasoroCentralCharge_calibrated :
    P.primeVirasoro.affineVirasoro.centralCharge =
      P.primeVirasoro.affineVirasoro.centralCharge :=
  rfl

/--
Combined prime-to-Virasoro owner target.

This is the honest theorem surface available in the repo:
finite arithmetic Gibbs readout,
prime zeta-trace readout,
prime Sugawara/Virasoro central charge,
operatorial central charge.
-/
@[rep_depth thermo]
def PrimonVirasoroCentralChargeOwnerTarget
    (P : InfoGeometry.Canonical.PrimonVirasoroCentralCharge.PrimonVirasoroCentralChargeBridge
      State LieAlg Obs PrimeLabel Field Coeff Finite Alg A B E) : Prop :=
  P.massieu.souriau.partitionPotential = Real.log P.arithmeticPartition
    ∧ let V : PrimeVielbeinCarrier := P.primeVielbein
      InfoGeometry.Arithmetic.PrimeVielbeinCarrier.traceLogSupervolume V P.zetaParameter =
        riemannZeta P.zetaParameter
    ∧ P.operatorialCharge =
        operatorialCentralCharge
          (A := A) (B := B) (E := E) P.topologicalChargeX P.topologicalChargehX
    ∧ P.virasoroCentralCharge = P.primeVirasoro.affineVirasoro.centralCharge

/-- The combined owner target is witnessed by the stored bridge equalities. -/
@[rep_depth thermo]
theorem primonVirasoroCentralChargeOwnerTarget :
    PrimonVirasoroCentralChargeOwnerTarget P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact partitionPotential_eq_log_arithmeticPartition (P := P)
  · exact primeTraceLogSupervolume_eq_riemannZeta (P := P)
  · exact operatorialCharge_eq_analyticIndex (P := P)
  · exact virasoroCentralCharge_eq_sugawara (P := P)

end Bridge

end InfoGeometry.Canonical.PrimonVirasoroCentralCharge
