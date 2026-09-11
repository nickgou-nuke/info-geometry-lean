import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.NonIsoConf3RankIngestion
import InfoGeometry.Projective.PenroseSpinTilingConfig

/-!
# Track-B finite arithmetic readouts

This owner exposes only finite definitions and theorems that are proved in
Lean.  The values are arithmetic inputs selected by the existing projective
owners; this file does not encode provenance records or pretend to verify an
external Macaulay2 computation.
-/

namespace InfoGeometry.Projective.MacaulayTrackBIngestion

open InfoGeometry.Projective.PenroseSpinTiling
open InfoGeometry.Projective.NonIsoConf3RankIngestion

/-! ## Arithmetic volume -/

/-- The finite field parameter used by the installed Track-B arithmetic readout. -/
def trackBPrimeField : ℕ := 3

/-- The candidate volume is the value of the native counting polynomial. -/
def trackBVolumeCount : ℤ :=
  tateMotivePolynomial trackBPrimeField

theorem trackB_volume_eq_tate_motive :
    trackBVolumeCount = tateMotivePolynomial trackBPrimeField := by
  rfl

theorem trackB_volume_value : trackBVolumeCount = 1296 := by
  rw [trackBVolumeCount, trackBPrimeField]
  exact pointCount_F3_verified

/-! ## Finite rank readout -/

/-- The installed local Betti signature. -/
def trackBLocalBettiNumbers : List ℕ := verifiedBettiNumbers

/-- The local rank obtained by summing that signature. -/
def trackBLocalRank : ℕ := trackBLocalBettiNumbers.sum

theorem trackB_local_rank_value : trackBLocalRank = 8 := by
  rw [trackBLocalRank, trackBLocalBettiNumbers]
  exact verifiedBettiNumbers_sum

/-- The configured finite tiling multiplicity. -/
def trackBTilingMultiplicity : ℕ := spinTilingMultiplicity

/-- The total finite rank obtained from the local rank and multiplicity. -/
def trackBTotalRank : ℕ := trackBTilingMultiplicity * trackBLocalRank

theorem trackB_total_rank_value : trackBTotalRank = 32 := by
  rw [trackBTotalRank, trackBTilingMultiplicity, trackBLocalRank]
  exact spinTiledDeRhamRank_eq_assumedTotalDeRhamRank

/-! ## Direct compatibility readouts -/

theorem trackB_volume_verified_against_tate_motive :
    trackBVolumeCount = tateMotivePolynomial trackBPrimeField := by
  exact trackB_volume_eq_tate_motive

theorem candidateBettiRank_local_rank : trackBLocalRank = 8 := by
  exact trackB_local_rank_value

theorem candidateBettiRank_spin_tiled_rank32 : trackBTotalRank = 32 := by
  exact trackB_total_rank_value

end InfoGeometry.Projective.MacaulayTrackBIngestion
