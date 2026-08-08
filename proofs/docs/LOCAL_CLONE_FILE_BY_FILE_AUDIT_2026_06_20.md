# Local clone file-by-file diff audit — 2026-06-20

Compared main clone `/home/goutev/auto` with external local clone `/home/goutev/repos/info-geometry-lean/external_refs/auto` after syncing main to GitHub.

Policy: choose the version that is buildable, theorem-honest, portable, and least likely to regress current `main`. External clone is behind `origin/main`, so external content is accepted only when it improves honesty/buildability without reintroducing stale paths, hard-coded local assumptions, or overclaiming prose.

## Summary

- Common differing files audited: 36
- External-only files audited: 31
- Main-only files: retained by default; they have no external alternative and current `main` builds.
- Generated/local files not merged: `all_lean_ast_graph.json`, `proofs/lake-manifest.json`, workspace `AGENTS.md`.

## Common differing files

| File | Verdict | Reason |
|---|---|---|
| `AGENTS.md` | keep main/local | Workspace policy file; not a proof/code candidate for clone merge. |
| `README.md` | keep main | Main README is newer, includes license/citation/AI collaboration and current build guidance; external removes current sections and points at stale package/path assumptions. |
| `all_lean_ast_graph.json` | skip generated | Generated graph artifact; should be regenerated from current source, not merged from stale clone. |
| `scripts/vacuity-linter.py` | keep main | Main linter is more conservative and graph-aware; external is older pattern-only implementation. |
| `proofs/ProjectiveWallpaperGaugePSA.lean` | keep main | Main has stronger finite checks (`La_sq`, `Lb_sq`, noncommutation) and builds. |
| `proofs/ingest_weyl_gauge.py` | keep main | Main has env-configurable Arango connection and graceful skip; external hard-codes localhost:8529 and overstates ingest success. |
| `proofs/BiquaternionMobiusSquashing.lean` | keep main | Main has additional theorem-honest finite anchors; external deletes them. |
| `proofs/ingest_soldering_triality.py` | keep main | Main is portable/graceful and labels nodes as roadmap annotations; external hard-codes Arango and overclaims. |
| `proofs/plot_pentagrid.py` | keep main | Main saves relative to the script and uses honest visualization title; external hard-codes a private path and overclaims Yang–Baxter/Penrose-limit meaning. |
| `proofs/run_omega_protocol_checks.py` | keep main | Main accumulates failures and supports non-strict reports; external regresses to immediate failure and removes `--strict`. |
| `proofs/GravitySoldering.lean` | keep main | Main reuses active `CartanWeylBogoliubovGravity` theorem instead of duplicating older matrix code/prose. |
| `proofs/BiquaternionKANnilpotent.lean` | keep main | Main is theorem-honest about finite nilpotent anchor; external overclaims analytic KAN/modular-flow closure. |
| `proofs/biquaternion_exp_closure.py` | keep main | External removes the current witness content. |
| `proofs/BraidNegativeIdentityMonodromy.lean` | keep main | Main includes Majorana bridge additions from audited integration and builds. |
| `proofs/PolynomialSymmetryOperators.lean` | keep main | Main includes Pauli quadratic closure and concise theorem statements; external has broader overclaiming prose. |
| `proofs/MinkowskiBiquaternion.lean` | keep main | Main is concise finite determinant/SL₂ certificate; external adds physical overclaims. |
| `proofs/ingest_master_equation.py` | keep main | Main has env-configurable, graceful Arango setup; external hard-codes localhost and assumes DB exists. |
| `proofs/CptFractalClosure.lean` | keep main | Main states finite CPT light-cone certificate; external uses stronger interpretive claims not proved. |
| `proofs/SouriauHestenesKrein.lean` | keep main | Main retains current theorem-honest buildable version; external is older/smaller. |
| `proofs/MorandiWallpaperCohomology.lean` | keep main | Main includes extension identity repairs from audited integration. |
| `proofs/LieFlowMatching.lean` | keep main after adopted hunk | External's proved `powerScheduleCompression` was adopted; main wording repaired to avoid “axioms” language. |
| `proofs/BiquaternionExpClosure.lean` | keep main | External deletes most current finite exponential closure content. |
| `proofs/ingest_anomalies.py` | keep main | Main is portable/graceful and labels graph entries as roadmap annotations; external hard-codes and overstates. |
| `proofs/WallpaperBulkAnyonProjection.lean` | keep main | Main includes projective wallpaper bridge/noncommuting facts and builds. |
| `proofs/python_arango_ingest.py` | keep main | Main supports multiple graph JSON formats/env vars and graceful no-DB behavior; external hard-codes paths/DB. |
| `proofs/lakefile.toml` | keep main | Main has current roots and absolute package paths used by current build; external removes many roots and reorders Majorana incorrectly for this repo. |
| `proofs/DiracFourierMellin.lean` | keep main | Main is concise finite Dirac/resolvent anchor; external adds unproved physical zero-mode interpretation. |
| `proofs/WallpaperIsometry.lean` | keep main | Main has simpler function-level theorem; external uses heavier structure and interpretive SUSY prose. |
| `proofs/ExceptionalBraidTopology.lean` | keep main | Main includes Majorana certificate strengthening and builds. |
| `proofs/biquaternion_mobius_squashing.py` | keep main | External deletes witness content. |
| `proofs/BraidCliffordIntegration.lean` | keep main after adopted hunk | External had useful Majorana strengthening/docstring hunk, adopted; rest is stale duplicate braid infrastructure. |
| `ui/src/App.jsx` | keep main | Main is current graph UI with mode switching/search/normalization; external is much older minimal viewer. |
| `ui/src/index.css` | keep main | External reintroduces Vite default centering; bad for full-screen graph UI. |
| `ui/src/App.css` | keep main | Main styles current graph UI; external is Vite/default-era and incompatible. |
| `proofs/tests/test_sympy_scripts.py` | keep main | Main has total time budget and skips heavy RH audit from smoke suite; external regresses runtime behavior. |

## External-only files

All external-only files below were temporarily copied into main and checked with `lake env lean`. None built as-is. Many had stale imports, parser errors, `sorry`, axioms, impossible typeclass assumptions, hard-coded old Mathlib imports, or overclaiming theorem names/prose. They were rejected and quarantined at `/home/goutev/.trash-auto/external-auto-unbuildable-20260620/`.

| File | Verdict |
|---|---|
| `proofs/BiquaternionLaplaceResolvent.lean` | reject: parser/field errors |
| `proofs/BiquaternionLogarithmMonodromy.lean` | reject: invalid calc/unsolved goals |
| `proofs/CayleySchreierGauge.lean` | reject: parser/tactic errors |
| `proofs/CliffordFiveFiveAnomaly.lean` | reject: typeclass failures |
| `proofs/CliffordInductiveTripotent.lean` | reject: stale missing Mathlib import |
| `proofs/CptTensorFractal.lean` | reject: stale missing Mathlib import |
| `proofs/CuntzKriegerKTheory.lean` | reject: parser/determinant errors |
| `proofs/DiracZeroModes.lean` | reject: parser/determinant errors |
| `proofs/FinalHolographicThesisSeal.lean` | reject: parser/typeclass/tactic errors |
| `proofs/HolographicDictionarySynthesis.lean` | reject: depends on rejected module |
| `proofs/HolographicErlangenCompletion.lean` | reject: parser/typeclass errors |
| `proofs/HolographicScaleExtinctions.lean` | reject: unsolved goals/omega failures |
| `proofs/KasparovKreinDoubling.lean` | reject: typeclass/sorry issues |
| `proofs/KleinGeometrySupergraded.lean` | reject: determinant/tactic errors |
| `proofs/KleinNilpotentThermo.lean` | reject: stale missing Mathlib import and `sorry` |
| `proofs/LiuCollinsAffineInvariance.lean` | reject: parser/missing theorem errors |
| `proofs/NonOrientableBraid.lean` | reject: unknown tactic/unsolved goals |
| `proofs/OctonionicStandardModel.lean` | reject: proof error |
| `proofs/OctonionMatrixObstruction.lean` | reject: noncomputable/invalid calc errors |
| `proofs/PaperwallDiscreteSUSY.lean` | reject: typeclass failures |
| `proofs/PaperwallSUSY.lean` | reject: typeclass failures |
| `proofs/PlatycosmKTheory.lean` | reject: parser/type mismatch and axiom |
| `proofs/ProjectiveCrystalTopology.lean` | reject: rewrite failure |
| `proofs/ProjectiveSymmetryAlgebra.lean` | reject: rewrite failure |
| `proofs/RGFixedPoint.lean` | reject: tactic/typeclass errors |
| `proofs/RP3Octupole.lean` | reject: missing `Real.pi` import/name errors |
| `proofs/SouriauGaussian.lean` | reject: parser/determinant errors |
| `proofs/SplitOctonionNilpotent.lean` | reject: noncomputable/tactic errors |
| `proofs/TripotentPenroseHolography.lean` | reject: parser/missing theorem errors |
| `proofs/TwistedHeckeKleinBottle.lean` | reject: stale missing Mathlib import |
| `proofs/WallpaperClassification.lean` | reject: stale missing Mathlib import |

## Adopted improvements from the external clone

Already integrated and validated in `main`:

- `proofs/MajoranaBraidGroup.lean`
- `proofs/majorana_braid_group.py`
- `proofs/WallpaperSemidirectProduct.lean`
- theorem-honesty repairs in Cuntz/Kasparov/KMS/Tomita/Lie-flow files
- Majorana and wallpaper bridge hunks in existing modules

## Validation used for accepted state

```bash
cd /home/goutev/auto/proofs && lake build
cd /home/goutev/auto && python proofs/CuntzKTheoryPairing.py
cd /home/goutev/auto && python proofs/KasparovKreinCategory.py
cd /home/goutev/auto && python proofs/tomita_kms_v4.py
cd /home/goutev/auto && PYTEST_SYMPY_MAX_SECONDS=300 python -m pytest proofs/tests/test_sympy_scripts.py -q
cd /home/goutev/auto && git diff --check
```
