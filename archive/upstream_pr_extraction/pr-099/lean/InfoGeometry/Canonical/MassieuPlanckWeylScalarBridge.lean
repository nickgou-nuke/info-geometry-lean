import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Canonical.SouriauOperatorialLogPotential

open scoped InnerProductSpace BigOperators

noncomputable section

/-!
# Massieu--Planck Weyl Scalar Bridge

This file is a theorem-safe scalar adapter between existing owner lanes:

* projective Weyl scale readouts from `Arithmetic.ProjectiveWeylGauge`;
* Souriau partition/Massieu normalization from `SouriauOperatorialLogPotential`;
* standard-form Ω-volume logarithmic potentials from `StandardFormOmegaVolumeBridge`;
* Souriau KL/Bregman readouts from `SouriauOperatorialLogPotential`.

It does not assert that a Weyl scale is automatically a partition function.
That identification is supplied as calibration data.
-/

namespace InfoGeometry.Canonical.MassieuPlanckWeylScalarBridge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Arithmetic.ProjectiveWeylGauge
open InfoGeometry.Canonical.SouriauOperatorialLogPotential

section WeylPartition

variable {State LieAlgebra Obs : Type*}
variable [AddMonoid LieAlgebra]
variable [NormedRing Obs] [NormedAlgebra ℝ Obs] [CompleteSpace Obs]

/--
Scalar calibration identifying the projective Weyl gauge readout with the
Souriau partition normalization.

The word "Planck" here is only a scalar normalization label: the Lean content is
`Z = WeylScale`, hence `Φ = log WeylScale`.
-/
@[rep_depth thermo]
structure MassieuPlanckWeylScalarCalibration where
  /-- Projective Weyl-gauge owner. -/
  weyl : ProjectiveWeylGaugeCalibration State

  /-- Souriau operatorial partition/Massieu owner. -/
  souriau : QuantumOperatorialSouriauFamily LieAlgebra Obs

  /-- The count profile used to produce the calibrated projective state. -/
  counts : CountProfile

  /-- Reference count profile for the projective relative/Weyl lane. -/
  reference : CountProfile

  /-- Finite support for the arithmetic/projective Weyl readout. -/
  support : Finset ℕ

  /-- Compact inverse-temperature coordinate used by the Weyl owner lane. -/
  u : ℝ

  /-- Calibration: the Weyl scalar is the Souriau partition function. -/
  weylScale_eq_partitionFunction :
    weyl.weylScaleReadout (weyl.stateOfProfiles counts reference support) u =
      souriau.partitionFunction

namespace MassieuPlanckWeylScalarCalibration

variable (B : MassieuPlanckWeylScalarCalibration (State := State)
    (LieAlgebra := LieAlgebra) (Obs := Obs))

/-- The calibrated projective state used by the bridge. -/
@[rep_depth thermo]
def projectiveState : State :=
  B.weyl.stateOfProfiles B.counts B.reference B.support

/-- The Weyl scalar readout at the installed state and temperature coordinate. -/
@[rep_depth thermo]
def weylScalar : ℝ :=
  B.weyl.weylScaleReadout B.projectiveState B.u

/-- The Weyl scalar is the Souriau partition function under the supplied calibration. -/
@[rep_depth thermo]
theorem weylScalar_eq_partitionFunction :
    B.weylScalar = B.souriau.partitionFunction :=
  B.weylScale_eq_partitionFunction

/--
Massieu/partition potential as logarithm of the Weyl scalar.

This is the formal version of "the Weyl gauge scalar is the thermodynamic
partition normalization".
-/
@[rep_depth thermo]
theorem partitionPotential_eq_log_weylScalar :
    B.souriau.partitionPotential = Real.log B.weylScalar := by
  rw [B.souriau.partitionPotential_eq_log_trace]
  rw [B.weylScalar_eq_partitionFunction]

/-- The Weyl scalar is positive because it is calibrated to a Souriau partition function. -/
@[rep_depth thermo]
theorem weylScalar_pos : 0 < B.weylScalar := by
  rw [B.weylScalar_eq_partitionFunction]
  exact B.souriau.partitionFunction_pos

/-- Re-export the Weyl factorization at the calibrated state. -/
@[rep_depth thermo]
theorem totalReadout_eq_weylScalar_mul_shapeCore :
    B.weyl.totalReadout B.projectiveState B.u =
      B.weylScalar * B.weyl.shapeCoreReadout B.projectiveState B.u := by
  simpa [projectiveState, weylScalar] using
    B.weyl.total_eq_scale_mul_shape B.counts B.reference B.support B.u

end MassieuPlanckWeylScalarCalibration

end WeylPartition

/-
The former scalar Bregman adapter was removed.  The canonical KL/Bregman
owner is the operatorial relative-modular layer; this file owns only the Weyl
partition calibration.
-/
/-

variable {State LieAlgebra LieDual Obs : Type*}

/--
Adapter tying the same Souriau partition/Massieu owner to an existing
KL-as-Bregman property.
-/
@[rep_depth thermo]
structure MassieuPlanckBregmanBridge extends
    MassieuPlanckWeylScalarCalibration (State := State) (LieAlgebra := LieAlgebra)
      (Obs := Obs) where
  /-- Existing Souriau KL/Bregman owner property. -/
  bregman : SouriauKLBregmanWitness State LieAlgebra LieDual

  /-- Calibration: both packets use the same Massieu potential. -/
  bregman_partitionPotential_eq :
    bregman.generator.souriau.partitionPotential = souriau.partitionPotential

namespace MassieuPlanckBregmanBridge

variable (B : MassieuPlanckBregmanBridge (State := State) (LieAlgebra := LieAlgebra)
    (LieDual := LieDual) (Obs := Obs))

/-- Owner readback: KL is the Souriau Bregman divergence expression. -/
@[rep_depth thermo]
theorem KL_eq_souriau_Bregman :
    B.bregman.klValue =
      B.bregman.alphaPartitionPotential
        - B.bregman.generator.souriau.partitionPotential
        - B.bregman.generator.dPhi B.bregman.alphaMinusBeta :=
  B.bregman.KL_eq_souriau_Bregman

/-- Same KL/Bregman readback, rewritten through the calibrated Weyl/Massieu scalar. -/
@[rep_depth thermo]
theorem KL_eq_weylMassieu_Bregman :
    B.bregman.klValue =
      B.bregman.alphaPartitionPotential
        - B.souriau.partitionPotential
        - B.bregman.generator.dPhi B.bregman.alphaMinusBeta := by
  rw [B.KL_eq_souriau_Bregman]
  rw [B.bregman_partitionPotential_eq]

/-- Same KL/Bregman readback, with the Massieu term shown as `log WeylScalar`. -/
@[rep_depth thermo]
theorem KL_eq_log_weylScalar_Bregman :
    B.bregman.klValue =
      B.bregman.alphaPartitionPotential
        - Real.log B.toMassieuPlanckWeylScalarCalibration.weylScalar
        - B.bregman.generator.dPhi B.bregman.alphaMinusBeta := by
  rw [B.KL_eq_weylMassieu_Bregman]
  rw [B.toMassieuPlanckWeylScalarCalibration.partitionPotential_eq_log_weylScalar]

end MassieuPlanckBregmanBridge

end Bregman
-/

end InfoGeometry.Canonical.MassieuPlanckWeylScalarBridge
