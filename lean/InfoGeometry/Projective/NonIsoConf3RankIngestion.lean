import InfoGeometry.Projective.PenroseSpinTilingConfig
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Non-isotropic `Conf₃` Rank Ingestion

#### BUCKET 1: CLOSED FINITE THEOREMS

- `candidateLocalBettiData_consistent`
- `candidateLocalBettiData_totalRank`
- `candidateLocalBettiData_spinTiled_rank32`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

- `rank_readback_from_consistent_data`
- `spin_tiled_rank_from_external_data`

#### BUCKET 3: OPEN CLOSURE DEBT

- Produce an external Macaulay2/Singular/Oaku output artifact for
  `C^8 \ V(q(a) q(b) q(a-b))` whose Betti list is independently auditable.
- Translate that artifact into a concrete `ExternalBettiData` value.
- Prove, outside this file, that the concrete value faithfully represents the
  actual algebraic de Rham cohomology computation.

This module is deliberately small.  It does not parse JSON inside Lean and it
does not turn a Boolean flag into a mathematical proof.  External computation
is represented as plain data; consistency, ambient dimension, and rank claims
enter as explicit theorem premises or closed arithmetic lemmas over concrete
lists.
-/

namespace InfoGeometry.Projective.NonIsoConf3RankIngestion

open InfoGeometry.Projective.PenroseSpinTiling

/-- Plain finite data extracted from an external Betti-number audit. -/
structure ExternalBettiData where
  ambientDim : ℕ
  bettiNumbers : List ℕ
  totalRank : ℕ

/-- Kernel-checkable arithmetic consistency for parsed Betti data. -/
def RankDataConsistent (data : ExternalBettiData) : Prop :=
  data.totalRank = data.bettiNumbers.sum

/-- The external data has the target ambient dimension for `C^8`. -/
def HasConf3AmbientDimension (data : ExternalBettiData) : Prop :=
  data.ambientDim = 8

/-- Read back the Betti list and total rank from explicitly consistent data. -/
theorem rank_readback_from_consistent_data
    (data : ExternalBettiData)
    (hConsistent : RankDataConsistent data) :
    ∃ bVals : List ℕ,
      data.bettiNumbers = bVals ∧ data.totalRank = bVals.sum := by
  refine ⟨data.bettiNumbers, rfl, ?_⟩
  exact hConsistent

/-- Conditional spin-tiling rank discharge from external local rank data. -/
theorem spin_tiled_rank_from_external_data
    (data : ExternalBettiData)
    (_hAmbient : HasConf3AmbientDimension data)
    (_hConsistent : RankDataConsistent data)
    (hRank : data.totalRank = 8) :
    data.totalRank * spinTilingMultiplicity = 32 := by
  rw [hRank]
  rfl

/-- Candidate local Betti vector currently used by the Penrose spin-tiling layer.

This is a concrete arithmetic fixture, not a claim that the D-module computation
has already returned this vector.
-/
def candidateLocalBettiData : ExternalBettiData where
  ambientDim := 8
  bettiNumbers := [1, 2, 1, 1, 2, 1, 0, 0, 0]
  totalRank := 8

/-- The candidate local Betti data has internally consistent rank arithmetic. -/
theorem candidateLocalBettiData_consistent :
    RankDataConsistent candidateLocalBettiData := by
  rfl

/-- The candidate local Betti data has local total rank `8`. -/
theorem candidateLocalBettiData_totalRank :
    candidateLocalBettiData.totalRank = 8 := by
  rfl

/-- If the external D-module computation returns the candidate local vector,
the spin-tiling multiplicity produces total rank `32`.
-/
theorem candidateLocalBettiData_spinTiled_rank32 :
    candidateLocalBettiData.totalRank * spinTilingMultiplicity = 32 := by
  exact spin_tiled_rank_from_external_data
    candidateLocalBettiData
    rfl
    candidateLocalBettiData_consistent
    candidateLocalBettiData_totalRank

end InfoGeometry.Projective.NonIsoConf3RankIngestion
