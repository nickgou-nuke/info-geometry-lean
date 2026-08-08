# External `auto` behind-sync inventory — 2026-06-20

This is the starting inventory for updating `/home/goutev/repos/info-geometry-lean/external_refs/auto` after the two committed-ahead changes were audited. It is deliberately file-by-file: do not mass overwrite the external worktree without using this manifest and the saved backup artifacts.

## Current facts

- External `origin/main`: `d7fb9448ce6361af7296c1b2032bf9dc2ef32930`
- External `HEAD`: `1ab19d5152112a6d17f161dcbc8a361c15af3170`
- Ahead/behind after fetch: `2	119`
- Pre-sync backup/status bundle: `/home/goutev/.trash-auto/external-auto-before-behind-sync-20260620-155834`

## Behind path classification against current `/home/goutev/auto`

- `same_as_current`: 679
- `missing_in_external_worktree`: 7
- `different_in_external_worktree`: 33

## Different/missing paths requiring explicit resolution

### missing_in_external_worktree

- `docs/EXTERNAL_AUTO_AHEAD_COMMITS_AUDIT_2026_06_20.md`
- `docs/EXTERNAL_CANDIDATE_NO_LOSS_AUDIT_2026_06_20.md`
- `preserved/external_auto_20260620/README.md`
- `preserved/external_auto_20260620/patches/external_HEAD_before_resolution.txt`
- `preserved/external_auto_20260620/patches/external_git_status_before_resolution.txt`
- `preserved/external_auto_20260620/patches/external_staged_before_resolution.diff`
- `preserved/external_auto_20260620/patches/external_uncommitted_before_resolution.diff`

### different_in_external_worktree

- `memory/2026-06-20.md`
- `proofs/BiquaternionLaplaceResolvent.lean`
- `proofs/BiquaternionLogarithmMonodromy.lean`
- `proofs/CayleySchreierGauge.lean`
- `proofs/CliffordFiveFiveAnomaly.lean`
- `proofs/CliffordInductiveTripotent.lean`
- `proofs/CptTensorFractal.lean`
- `proofs/CuntzKriegerKTheory.lean`
- `proofs/DiracZeroModes.lean`
- `proofs/FinalHolographicThesisSeal.lean`
- `proofs/HolographicDictionarySynthesis.lean`
- `proofs/HolographicErlangenCompletion.lean`
- `proofs/HolographicScaleExtinctions.lean`
- `proofs/KasparovKreinDoubling.lean`
- `proofs/KleinGeometrySupergraded.lean`
- `proofs/KleinNilpotentThermo.lean`
- `proofs/LiuCollinsAffineInvariance.lean`
- `proofs/NonOrientableBraid.lean`
- `proofs/OctonionMatrixObstruction.lean`
- `proofs/OctonionicStandardModel.lean`
- `proofs/PaperwallDiscreteSUSY.lean`
- `proofs/PaperwallSUSY.lean`
- `proofs/PlatycosmKTheory.lean`
- `proofs/ProjectiveCrystalTopology.lean`
- `proofs/ProjectiveSymmetryAlgebra.lean`
- `proofs/RGFixedPoint.lean`
- `proofs/RP3Octupole.lean`
- `proofs/SouriauGaussian.lean`
- `proofs/SplitOctonionNilpotent.lean`
- `proofs/TripotentPenroseHolography.lean`
- `proofs/TwistedHeckeKleinBottle.lean`
- `proofs/WallpaperClassification.lean`
- `proofs/lakefile.toml`

## Resolution rule

- `same_as_current`: safe to let Git track from `origin/main`; content already matches current main.
- `missing_in_external_worktree`: copy from current main or accept from `origin/main` after verifying path intent.
- `different_in_external_worktree`: compare file-by-file. The 31 Lean candidate paths are already covered by `docs/EXTERNAL_CANDIDATE_NO_LOSS_AUDIT_2026_06_20.md`; active current-main repaired modules should win, with originals recoverable from git history/backups.
