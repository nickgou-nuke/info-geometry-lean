# Local clone diff audit — 2026-06-20

Compared `/home/goutev/auto` against `/home/goutev/repos/info-geometry-lean/external_refs/auto`.

Policy: keep only buildable, theorem-honest changes. Do not bulk-merge the external clone because it is substantially behind `origin/main` and contains many unbuildable old modules.

## Adopted common-file improvements

These external versions or hunks were better and now build in the main repo:

- `proofs/CuntzKTheoryPairing.lean` — replaced informal O₂/K₀ language with proof-carrying `O2K0Trivial`, added theorem-honest trivial-K₀ bridge.
- `proofs/CuntzKTheoryPairing.py` — witness now says the zero K₀ hypothesis is supplied, not computed.
- `proofs/FibonacciCliffordBridge.lean` — minor robustness/section close.
- `proofs/GT_FromText.lean` — removed axiomized/placeholder theorem stubs and kept theorem-backed extracted seeds.
- `proofs/HilbertPolyaBivariant.lean` — renamed/refocused the off-axis firewall as a categorical non-factorization theorem, not an RH claim.
- `proofs/KanCayley.lean` — added proved thermal Cayley limit theorem.
- `proofs/KasparovKreinCategory.lean` — made O₂ boundary carrier an alias to the proof-trivial K₀ model and replaced vacuous anomaly-collapse-from-impossible-chain theorem with a non-existence theorem.
- `proofs/KasparovKreinCategory.py` — witness now mirrors the no-chain firewall.
- `proofs/KreinVacuumKMSBridge.lean` — replaced top-level KMS axioms with proof-carrying `CyclicKMSSector` and concrete finite trace KMS sector.
- `proofs/LieFlowCompilerBridge.lean` — wording/no-new-math cleanup.
- `proofs/LieFlowMatching.lean` — replaced `powerScheduleCompression` axiom with a Lean proof.
- `proofs/test_simp.lean` — made the field inverse assumption explicit.
- `proofs/tomita_kms_v4.lean` — replaced GNS/Tomita `PUnit` placeholders with finite proof-carrying structures and concrete finite matrix witnesses.
- `proofs/tomita_kms_v4.py` — witness now checks finite left-regular GNS, finite Tomita involution, and finite trace KMS cyclicity.
- `proofs/BraidCliffordIntegration.lean` — kept current main implementation and adopted only the external strengthening theorem/docstring improvements.

## Already adopted in the previous integration pass

- `proofs/MajoranaBraidGroup.lean`
- `proofs/majorana_braid_group.py`
- `proofs/WallpaperSemidirectProduct.lean`

Plus bridges into braid/wallpaper modules and lake roots.

## Rejected/quarantined external-only files

The following files existed only in the external clone. Each was tested with `lake env lean` after temporary copy into the main repo. None built as-is, and many contained stale imports, parser errors, `sorry`, axioms, impossible typeclass assumptions, or overclaiming theorem names. They were not imported and were moved to:

`/home/goutev/.trash-auto/external-auto-unbuildable-20260620/`

- `BiquaternionLaplaceResolvent.lean`
- `BiquaternionLogarithmMonodromy.lean`
- `CayleySchreierGauge.lean`
- `CliffordFiveFiveAnomaly.lean`
- `CliffordInductiveTripotent.lean`
- `CptTensorFractal.lean`
- `CuntzKriegerKTheory.lean`
- `DiracZeroModes.lean`
- `FinalHolographicThesisSeal.lean`
- `HolographicDictionarySynthesis.lean`
- `HolographicErlangenCompletion.lean`
- `HolographicScaleExtinctions.lean`
- `KasparovKreinDoubling.lean`
- `KleinGeometrySupergraded.lean`
- `KleinNilpotentThermo.lean`
- `LiuCollinsAffineInvariance.lean`
- `NonOrientableBraid.lean`
- `OctonionicStandardModel.lean`
- `OctonionMatrixObstruction.lean`
- `PaperwallDiscreteSUSY.lean`
- `PaperwallSUSY.lean`
- `PlatycosmKTheory.lean`
- `ProjectiveCrystalTopology.lean`
- `ProjectiveSymmetryAlgebra.lean`
- `RGFixedPoint.lean`
- `RP3Octupole.lean`
- `SouriauGaussian.lean`
- `SplitOctonionNilpotent.lean`
- `TripotentPenroseHolography.lean`
- `TwistedHeckeKleinBottle.lean`
- `WallpaperClassification.lean`

## Validation

- `cd proofs && lake build`
- `python proofs/CuntzKTheoryPairing.py`
- `python proofs/KasparovKreinCategory.py`
- `python proofs/tomita_kms_v4.py`
- `PYTEST_SYMPY_MAX_SECONDS=300 python -m pytest proofs/tests/test_sympy_scripts.py -q`
- `git diff --check`
