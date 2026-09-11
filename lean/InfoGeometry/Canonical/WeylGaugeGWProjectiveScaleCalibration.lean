import InfoGeometry.Canonical.WeylGaugeOperatorLift
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GromovWittenErlangen.GWProjectiveCountCalibration
import InfoGeometry.Volume.DeterminantBundle

/-!
# Two-sheet Weyl/GW projective-scale calibration

This owner keeps the common and relative Weyl channels separate.  A positive
GW projective-count packet is attached independently to each sheet, and the
primitive calibration fields identify the two sheet volume scales with the two
finite partition readouts.  The ratio and logarithmic identities below are
derived from those fields.

No equality between an operator determinant character and a GW partition is
asserted without these calibration fields.  No Gromov--Witten localization,
holography, or AdS/CFT theorem is constructed here.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.GromovWittenErlangen
open InfoGeometry.Volume.DeterminantBundle
open InfoGeometry.Canonical.RestrictedVolumeCharacter
open InfoGeometry.Canonical.WeylGaugeOperatorLift

noncomputable section

variable {E G T Target Coeff : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The common Weyl scale is the geometric mean of the two sheet scales. -/
def commonVolumeScale (g : LiftedSheetAut (E := E)) : ℝ :=
  Real.sqrt
    (volumeScale g.plus.toLinearEquiv * volumeScale g.minus.toLinearEquiv)

/-- Primitive two-sheet calibration data. -/
structure WeylGWTwoSheetCalibration where
  g : LiftedSheetAut (E := E)
  beta : ℝ
  plusCounts : GWProjectiveCountCalibration G T Target Coeff
  minusCounts : GWProjectiveCountCalibration G T Target Coeff
  plusPartition_pos : 0 < plusCounts.finitePartition beta
  minusPartition_pos : 0 < minusCounts.finitePartition beta
  plusVolume_eq :
    volumeScale g.plus.toLinearEquiv = plusCounts.finitePartition beta
  minusVolume_eq :
    volumeScale g.minus.toLinearEquiv = minusCounts.finitePartition beta

namespace WeylGWTwoSheetCalibration

variable (B : WeylGWTwoSheetCalibration
  (E := E) (G := G) (T := T) (Target := Target) (Coeff := Coeff))

theorem commonVolumeScale_pos :
    0 < commonVolumeScale B.g := by
  unfold commonVolumeScale
  exact Real.sqrt_pos.2 (mul_pos
    (RestrictedSheetEquiv.volumeScale_pos (f := B.g.plus.toLinearEquiv))
    (RestrictedSheetEquiv.volumeScale_pos (f := B.g.minus.toLinearEquiv)))

def relativePartitionRatio : ℝ :=
  B.plusCounts.finitePartition B.beta /
    B.minusCounts.finitePartition B.beta

theorem relativePartitionRatio_pos :
    0 < B.relativePartitionRatio := by
  unfold relativePartitionRatio
  exact div_pos B.plusPartition_pos B.minusPartition_pos

theorem relativeVolumeScale_eq_partition_ratio :
    LiftedSheetAut.relativeVolumeScale B.g = B.relativePartitionRatio := by
  unfold LiftedSheetAut.relativeVolumeScale
  unfold LiftedSheetAut.toRestrictedSheetEquiv
  unfold RestrictedSheetEquiv.restrictedVolumeScale
  unfold RestrictedSheetEquiv.plusSheetVolumeScale
    RestrictedSheetEquiv.minusSheetVolumeScale
  rw [B.plusVolume_eq, B.minusVolume_eq]
  rfl

theorem logRelativeVolumePotential_eq_log_partition_ratio :
    LiftedSheetAut.logRelativeVolumePotential B.g =
      Real.log B.relativePartitionRatio := by
  rw [LiftedSheetAut.logRelativeVolumePotential,
    B.relativeVolumeScale_eq_partition_ratio]

theorem commonLogCoordinate_eq_partition_log_average :
    LiftedSheetAut.commonLogCoordinate B.g =
      (Real.log (B.plusCounts.finitePartition B.beta) +
        Real.log (B.minusCounts.finitePartition B.beta)) / 2 := by
  unfold LiftedSheetAut.commonLogCoordinate LiftedSheetAut.logPlusVolume
    LiftedSheetAut.logMinusVolume
  rw [B.plusVolume_eq, B.minusVolume_eq]

theorem commonLogCoordinate_eq_log_commonVolumeScale :
    LiftedSheetAut.commonLogCoordinate B.g =
      Real.log (commonVolumeScale B.g) := by
  unfold LiftedSheetAut.commonLogCoordinate LiftedSheetAut.logPlusVolume
    LiftedSheetAut.logMinusVolume commonVolumeScale
  have hp := (RestrictedSheetEquiv.volumeScale_pos
      (f := B.g.plus.toLinearEquiv)).ne'
  have hm := (RestrictedSheetEquiv.volumeScale_pos
      (f := B.g.minus.toLinearEquiv)).ne'
  rw [Real.log_sqrt]
  · rw [Real.log_mul hp hm]
  · exact le_of_lt (mul_pos
      (RestrictedSheetEquiv.volumeScale_pos (f := B.g.plus.toLinearEquiv))
      (RestrictedSheetEquiv.volumeScale_pos (f := B.g.minus.toLinearEquiv)))

theorem commonVolumeScale_eq_partition_geometricMean :
    commonVolumeScale B.g =
      Real.sqrt (B.plusCounts.finitePartition B.beta *
        B.minusCounts.finitePartition B.beta) := by
  unfold commonVolumeScale
  rw [B.plusVolume_eq, B.minusVolume_eq]

theorem relativeLogCoordinate_eq_partition_log_difference :
    LiftedSheetAut.relativeLogCoordinate B.g =
      (Real.log (B.plusCounts.finitePartition B.beta) -
        Real.log (B.minusCounts.finitePartition B.beta)) / 2 := by
  unfold LiftedSheetAut.relativeLogCoordinate LiftedSheetAut.logPlusVolume
    LiftedSheetAut.logMinusVolume
  rw [B.plusVolume_eq, B.minusVolume_eq]

theorem logRelativeVolumePotential_eq_two_mul_relativeLogCoordinate :
    LiftedSheetAut.logRelativeVolumePotential B.g =
      (2 : ℝ) * LiftedSheetAut.relativeLogCoordinate B.g := by
  exact LiftedSheetAut.logRelativeVolumePotential_eq_two_mul_relativeLogCoordinate B.g

end WeylGWTwoSheetCalibration

end

end InfoGeometry.Canonical
