import Mathlib
import InfoGeometry.Projective.NonIsoConf3RankIngestion
import InfoGeometry.Projective.PenroseSpinTilingConfig

/-!
# Macaulay2 Track B Certificate Boundary

This module records the Track B evidence boundary as explicit Lean data.
It does not parse JSON at compile time and it does not certify that an external
Macaulay2 run succeeded.  External provenance, status, and hashes are kept as
ordinary data; the kernel-checked content is limited to finite arithmetic
readbacks against the existing owner configurations.

The closed theorem surface is:

* the transcribed arithmetic volume `1296` matches `tateMotivePolynomial 3`;
* the candidate local Betti data has ambient dimension `8`, rank `8`, and
  spin-tiling total rank `32`.

The file intentionally separates those two certificates.
-/

namespace MacaulayTrackBIngestion

open InfoGeometry.Projective.PenroseSpinTiling
open InfoGeometry.Projective.NonIsoConf3RankIngestion

/-- Provenance metadata for a transcribed external evidence payload. -/
structure EvidenceProvenance where
  schema : String
  source : String
  engine : String
  sha256 : String
  status : String
  isVerified : Bool

/-- Plain finite data extracted from the Track B arithmetic-volume audit. -/
structure ExternalMacaulayTrackBData where
  primeField : ℕ
  volumeCount : ℤ

/--
The ingested Track B arithmetic data over `F_3`.

This is a transcribed finite payload.  The theorem below proves only that this
payload agrees with the candidate Tate-motive polynomial already owned by
`PenroseSpinTilingConfig`.
-/
def ingestedTrackBDataF3 : ExternalMacaulayTrackBData where
  primeField := 3
  volumeCount := 1296

/-- A kernel-checkable arithmetic-volume certificate. -/
structure ArithmeticVolumeCertificate where
  provenance : EvidenceProvenance
  data : ExternalMacaulayTrackBData
  matchesCandidate :
    data.volumeCount = tateMotivePolynomial data.primeField

/-- Candidate local Betti-rank certificate, kept separate from volume evidence. -/
structure BettiRankCertificate where
  provenance : EvidenceProvenance
  data : ExternalBettiData
  ambient8 : HasConf3AmbientDimension data
  consistent : RankDataConsistent data
  localRank8 : data.totalRank = 8

/-- The transcribed arithmetic-volume payload provenance. -/
def arithmeticVolumeF3Provenance : EvidenceProvenance where
  schema := "track_b_arithmetic_volume.v1"
  source := "formalizations/compute_derham_track_b.py"
  engine := "Macaulay2/BernsteinSato-or-transcribed-arithmetic"
  sha256 := "086fd0d7d123008011dfd48ee5552bb8692efa570299b3357f9282094f2131d0"
  status := "transcribed"
  isVerified := false

/-- The transcribed candidate Betti-rank payload provenance. -/
def candidateBettiRankProvenance : EvidenceProvenance where
  schema := "non_iso_conf3_rank32_external_audit.v1"
  source := "proofs/non_iso_conf3_rank32_external_audit.py"
  engine := "Macaulay2/BernsteinSato"
  sha256 := "095d85555b40d82e7fc255a383d3854f1af0442ab30f98b39d4bba1280cda17e"
  status := "candidate-fixture"
  isVerified := false

/-- Kernel-checked arithmetic certificate for the `F_3` Track B volume datum. -/
def arithmeticVolumeF3Certificate : ArithmeticVolumeCertificate where
  provenance := arithmeticVolumeF3Provenance
  data := ingestedTrackBDataF3
  matchesCandidate := pointCount_F3_verified.symm

/-- Kernel-checked candidate Betti-rank certificate used by the spin-tiling layer. -/
def candidateBettiRankCertificate : BettiRankCertificate where
  provenance := candidateBettiRankProvenance
  data := candidateLocalBettiData
  ambient8 := rfl
  consistent := candidateLocalBettiData_consistent
  localRank8 := candidateLocalBettiData_totalRank

/-- The arithmetic certificate is currently a transcribed payload, not a backend proof. -/
theorem arithmeticVolumeF3_status :
    arithmeticVolumeF3Certificate.provenance.status = "transcribed" := by
  rfl

/-- The arithmetic certificate has no positive external-run verification flag. -/
theorem arithmeticVolumeF3_not_external_verified :
    arithmeticVolumeF3Certificate.provenance.isVerified = false := by
  rfl

/-- Read back the arithmetic certificate against the candidate Tate-motive polynomial. -/
theorem arithmeticVolumeF3_matches_tate_motive :
    arithmeticVolumeF3Certificate.data.volumeCount =
      tateMotivePolynomial arithmeticVolumeF3Certificate.data.primeField := by
  exact arithmeticVolumeF3Certificate.matchesCandidate

/--
Compatibility theorem: the transcribed Track B arithmetic datum matches the
candidate Tate-motive polynomial at `q = 3`.
-/
theorem trackB_volume_verified_against_tate_motive :
    ingestedTrackBDataF3.volumeCount = tateMotivePolynomial ingestedTrackBDataF3.primeField := by
  exact arithmeticVolumeF3_matches_tate_motive

/-- The candidate Betti certificate is explicitly marked as a fixture. -/
theorem candidateBettiRank_status :
    candidateBettiRankCertificate.provenance.status = "candidate-fixture" := by
  rfl

/-- The candidate Betti certificate has no positive external-run verification flag. -/
theorem candidateBettiRank_not_external_verified :
    candidateBettiRankCertificate.provenance.isVerified = false := by
  rfl

/-- Read back the candidate Betti local rank. -/
theorem candidateBettiRank_local_rank :
    candidateBettiRankCertificate.data.totalRank = 8 := by
  exact candidateBettiRankCertificate.localRank8

/-- Read back the spin-tiled rank-32 consequence from the candidate Betti certificate. -/
theorem candidateBettiRank_spin_tiled_rank32 :
    candidateBettiRankCertificate.data.totalRank * spinTilingMultiplicity = 32 := by
  exact spin_tiled_rank_from_external_data
    candidateBettiRankCertificate.data
    candidateBettiRankCertificate.ambient8
    candidateBettiRankCertificate.consistent
    candidateBettiRankCertificate.localRank8

/-- Combined Track B certificate boundary consumed by downstream readout modules. -/
structure TrackBCertificateBoundary where
  arithmeticVolume : ArithmeticVolumeCertificate
  bettiRank : BettiRankCertificate

/-- The canonical theorem-honest Track B boundary currently available in Lean. -/
def canonicalTrackBBoundary : TrackBCertificateBoundary where
  arithmeticVolume := arithmeticVolumeF3Certificate
  bettiRank := candidateBettiRankCertificate

/-- The canonical boundary reads back the arithmetic `F_3` volume. -/
theorem canonicalTrackBBoundary_arithmetic :
    canonicalTrackBBoundary.arithmeticVolume.data.volumeCount =
      tateMotivePolynomial canonicalTrackBBoundary.arithmeticVolume.data.primeField := by
  exact canonicalTrackBBoundary.arithmeticVolume.matchesCandidate

/-- The canonical boundary reads back the candidate spin-tiled rank. -/
theorem canonicalTrackBBoundary_spin_tiled_rank32 :
    canonicalTrackBBoundary.bettiRank.data.totalRank * spinTilingMultiplicity = 32 := by
  exact spin_tiled_rank_from_external_data
    canonicalTrackBBoundary.bettiRank.data
    canonicalTrackBBoundary.bettiRank.ambient8
    canonicalTrackBBoundary.bettiRank.consistent
    canonicalTrackBBoundary.bettiRank.localRank8

end MacaulayTrackBIngestion
