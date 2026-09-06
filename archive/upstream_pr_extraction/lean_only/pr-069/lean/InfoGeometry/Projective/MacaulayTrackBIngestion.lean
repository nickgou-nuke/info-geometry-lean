import Mathlib.Tactic
import InfoGeometry.Projective.NonIsoConf3RankIngestion
import InfoGeometry.Projective.PenroseSpinTilingConfig

/-!
# Macaulay2 Track B Certificate Boundary

This module records the Track B source-metadata boundary as explicit Lean data.
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

namespace InfoGeometry.Projective.MacaulayTrackBIngestion

open InfoGeometry.Projective.PenroseSpinTiling
open InfoGeometry.Projective.NonIsoConf3RankIngestion

/-! ## Native metadata status -/

inductive DataStatus where
  | verified
  | transcribed
  | candidateFixture
  deriving DecidableEq, Repr

/-- Metadata for a transcribed external payload. -/
structure SourceMetadata where
  schema : String
  source : String
  engine : String
  sha256 : String
  status : DataStatus

/-- External verification is a proposition derived from the native status. -/
def SourceMetadata.hasVerifiedStatus (P : SourceMetadata) : Prop :=
  P.status = DataStatus.verified

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

/-- A kernel-checkable arithmetic-volume property. -/
abbrev ArithmeticVolumeCertificate : Type :=
  Σ' _metadata : SourceMetadata,
    Σ' data : ExternalMacaulayTrackBData,
      data.volumeCount = tateMotivePolynomial data.primeField

namespace ArithmeticVolumeCertificate

abbrev metadata (C : ArithmeticVolumeCertificate) : SourceMetadata := C.1
abbrev data (C : ArithmeticVolumeCertificate) : ExternalMacaulayTrackBData := C.2.1
abbrev matchesCandidate (C : ArithmeticVolumeCertificate) :
    C.data.volumeCount = tateMotivePolynomial C.data.primeField := C.2.2

end ArithmeticVolumeCertificate

/-- Candidate local Betti-rank property, kept separate from the volume property. -/
abbrev BettiRankCertificate : Type :=
  Σ' _metadata : SourceMetadata,
    Σ' data : ExternalBettiData,
      HasConf3AmbientDimension data ∧
        RankDataConsistent data ∧ data.totalRank = 8

namespace BettiRankCertificate

abbrev metadata (C : BettiRankCertificate) : SourceMetadata := C.1
abbrev data (C : BettiRankCertificate) : ExternalBettiData := C.2.1
abbrev ambient8 (C : BettiRankCertificate) : HasConf3AmbientDimension C.data := C.2.2.1
abbrev consistent (C : BettiRankCertificate) : RankDataConsistent C.data := C.2.2.2.1
abbrev localRank8 (C : BettiRankCertificate) : C.data.totalRank = 8 := C.2.2.2.2

end BettiRankCertificate

/-- Metadata for the transcribed arithmetic-volume payload. -/
def arithmeticVolumeF3Metadata : SourceMetadata where
  schema := "track_b_arithmetic_volume.v1"
  source := "formalizations/compute_derham_track_b.py"
  engine := "Macaulay2/BernsteinSato-or-transcribed-arithmetic"
  sha256 := "086fd0d7d123008011dfd48ee5552bb8692efa570299b3357f9282094f2131d0"
  status := DataStatus.transcribed

/-- Metadata for the transcribed candidate Betti-rank payload. -/
def candidateBettiRankMetadata : SourceMetadata where
  schema := "non_iso_conf3_rank32_external_audit.v1"
  source := "proofs/non_iso_conf3_rank32_external_audit.py"
  engine := "Macaulay2/BernsteinSato"
  sha256 := "095d85555b40d82e7fc255a383d3854f1af0442ab30f98b39d4bba1280cda17e"
  status := DataStatus.candidateFixture

/-- Kernel-checked arithmetic property for the `F_3` Track B volume datum. -/
def arithmeticVolumeF3Certificate : ArithmeticVolumeCertificate :=
  ⟨arithmeticVolumeF3Metadata, ingestedTrackBDataF3, pointCount_F3_verified.symm⟩

/-- Kernel-checked candidate Betti-rank property used by the spin-tiling layer. -/
def candidateBettiRankCertificate : BettiRankCertificate :=
  ⟨candidateBettiRankMetadata, candidateLocalBettiData,
    rfl, candidateLocalBettiData_consistent, candidateLocalBettiData_totalRank⟩

/-- The arithmetic property is currently a transcribed payload, not a backend proof. -/
theorem arithmeticVolumeF3_status :
    arithmeticVolumeF3Certificate.metadata.status = DataStatus.transcribed := by
  rfl

/-- The arithmetic property has no positive external-run verification flag. -/
theorem arithmeticVolumeF3_not_external_verified :
    ¬ arithmeticVolumeF3Certificate.metadata.hasVerifiedStatus := by
  change ¬ DataStatus.transcribed = DataStatus.verified
  decide

/-- Read back the arithmetic property against the candidate Tate-motive polynomial. -/
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

/-- The candidate Betti property is explicitly marked as a fixture. -/
theorem candidateBettiRank_status :
    candidateBettiRankCertificate.metadata.status = DataStatus.candidateFixture := by
  rfl

/-- The candidate Betti property has no positive external-run verification flag. -/
theorem candidateBettiRank_not_external_verified :
    ¬ candidateBettiRankCertificate.metadata.hasVerifiedStatus := by
  change ¬ DataStatus.candidateFixture = DataStatus.verified
  decide

/-- Read back the candidate Betti local rank. -/
theorem candidateBettiRank_local_rank :
    candidateBettiRankCertificate.data.totalRank = 8 := by
  exact candidateBettiRankCertificate.localRank8

/-- Read back the spin-tiled rank-32 consequence from the candidate Betti property. -/
theorem candidateBettiRank_spin_tiled_rank32 :
    candidateBettiRankCertificate.data.totalRank * spinTilingMultiplicity = 32 := by
  exact spin_tiled_rank_from_external_data
    candidateBettiRankCertificate.data
    candidateBettiRankCertificate.ambient8
    candidateBettiRankCertificate.consistent
    candidateBettiRankCertificate.localRank8

/-- Combined Track B property boundary consumed by downstream readout modules. -/
abbrev TrackBCertificateBoundary : Type :=
  ArithmeticVolumeCertificate × BettiRankCertificate

namespace TrackBCertificateBoundary

abbrev arithmeticVolume (C : TrackBCertificateBoundary) : ArithmeticVolumeCertificate := C.1
abbrev bettiRank (C : TrackBCertificateBoundary) : BettiRankCertificate := C.2

end TrackBCertificateBoundary

/-- The canonical theorem-honest Track B boundary currently available in Lean. -/
def canonicalTrackBBoundary : TrackBCertificateBoundary :=
  (arithmeticVolumeF3Certificate, candidateBettiRankCertificate)

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

end InfoGeometry.Projective.MacaulayTrackBIngestion
