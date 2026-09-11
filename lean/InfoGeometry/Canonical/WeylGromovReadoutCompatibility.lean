import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

/-!
# Weyl/Gromov readout compatibility

This owner records a narrowly typed compatibility contract between a Weyl
readout and a finite arithmetic/Gromov--Witten-inspired readout. The fields
are hypotheses: this file does not construct Gromov--Witten invariants, a
Weyl gauge theory, a holographic correspondence, or an AdS/CFT theorem.

The positivity field is included because a logarithmic potential is only a
real logarithm of a positive partition readout in the intended application.
All downstream results are genuine consequences of the supplied contract.
-/

variable {E : Type*}

/-- Compatibility data for two scalar readouts on a common parameter type. -/
structure WeylGromovReadoutCompatibility
    (E : Type*)
    (relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition : E → ℝ) where
  /-- The Weyl scale and finite partition readouts agree pointwise. -/
  scale_eq_partition :
    ∀ e, relativeVolumeScale e = finiteArithmeticPartition e
  /-- The finite partition readout lies in the domain of the real logarithm. -/
  partition_pos :
    ∀ e, 0 < finiteArithmeticPartition e
  /-- The Weyl logarithmic potential is the logarithm of the partition readout. -/
  log_potential_eq :
    ∀ e, logRelativeVolumePotential e =
      Real.log (finiteArithmeticPartition e)

namespace WeylGromovReadoutCompatibility

theorem weyl_scale_eq_partition
    {relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition : E → ℝ}
    (B : WeylGromovReadoutCompatibility
      E relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition)
    (e : E) :
    relativeVolumeScale e = finiteArithmeticPartition e :=
  B.scale_eq_partition e

theorem partition_pos_readout
    {relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition : E → ℝ}
    (B : WeylGromovReadoutCompatibility
      E relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition)
    (e : E) :
    0 < finiteArithmeticPartition e :=
  B.partition_pos e

theorem weyl_log_potential_eq
    {relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition : E → ℝ}
    (B : WeylGromovReadoutCompatibility
      E relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition)
    (e : E) :
    logRelativeVolumePotential e =
      Real.log (finiteArithmeticPartition e) :=
  B.log_potential_eq e

theorem log_partition_exp_eq
    {relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition : E → ℝ}
    (B : WeylGromovReadoutCompatibility
      E relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition)
    (e : E) :
    Real.exp (logRelativeVolumePotential e) =
      finiteArithmeticPartition e := by
  rw [B.log_potential_eq e]
  exact Real.exp_log (B.partition_pos e)

theorem scale_eq_exp_log_potential
    {relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition : E → ℝ}
    (B : WeylGromovReadoutCompatibility
      E relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition)
    (e : E) :
    relativeVolumeScale e = Real.exp (logRelativeVolumePotential e) := by
  rw [B.scale_eq_partition e, B.log_potential_eq e]
  exact (Real.exp_log (B.partition_pos e)).symm

theorem log_potential_eq_log_scale
    {relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition : E → ℝ}
    (B : WeylGromovReadoutCompatibility
      E relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition)
    (e : E) :
    logRelativeVolumePotential e = Real.log (relativeVolumeScale e) := by
  rw [B.log_potential_eq e, B.scale_eq_partition e]

/-- A common half-log coordinate agrees with a Massieu readout when both
readouts use the same partition logarithm. -/
theorem half_log_coordinate_eq_massieu
    {relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition : E → ℝ}
    (B : WeylGromovReadoutCompatibility
      E relativeVolumeScale logRelativeVolumePotential
      finiteArithmeticPartition)
    (commonLogCoordinate massieuPotential : E → ℝ)
    (e : E)
    (hcommon : commonLogCoordinate e =
      logRelativeVolumePotential e / 2)
    (hmassieu : massieuPotential e =
      Real.log (finiteArithmeticPartition e) / 2) :
    commonLogCoordinate e = massieuPotential e := by
  rw [hcommon, hmassieu, B.log_potential_eq e]

end WeylGromovReadoutCompatibility

end InfoGeometry.Canonical
