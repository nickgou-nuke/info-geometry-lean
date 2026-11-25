# Final independent acceptance reconciliation

**PASS for the completed isolated exact-pin compilation, native declaration audit, source/artifact identity, and fresh staged source-gate evidence.** No discrepancy remains in the reviewed Lean sources, compiler inputs, artifacts, verifier controls, dependency pins, or staged Lean files.

Reviewed on 2026-11-25 UTC against baseline `fe24e350b08fdea04f74c0748ef9fd9417c47529`. This review ran no Lean/Lake command, acquired no build lock, and modified no accepted repository file. The full checked inventory and read-only reconciliation script are session-local evidence at `/workspace/scratch/3288f93e1961/candidates/FINAL_QA_DATA.json` and `/workspace/scratch/3288f93e1961/candidates/reconcile_final_qa.py`.

## Verified evidence

- All **12 subprocess receipts** record exit zero: environment probe, compiler version, nine project compilations, and native audit. All current log hashes match. All nine project compilation logs are empty. Exact compiler arguments, output paths, and topological import order reconcile.
- All **nine project sources** match their recorded hashes, current repository bytes, staged bytes, and copied compiler inputs. The four inherited sources also match baseline HEAD. All **nine compiled artifacts** match their receipts, including every imported-project-artifact binding.
- All **11 control/runtime fingerprints** match current files; repository controls also match the index. Lean is the recorded **4.34.1** executable. Mathlib is clean at `d13f23b723b8a846827a245b89c10fc7d3f11612`; all eight dependencies are clean and agree with both manifests and the receipt. Search paths stay within the reviewed artifact/runtime roots.
- A fresh execution of the repository Python parser exactly reproduces the complete recorded native-audit result, including declaration names. The native log contains 108 distinct declarations, four module records, and one final PASS summary: **94 theorems and 14 definitions**, including generated declarations.

| Owner | Declarations |
|---|---:|
| `InfoGeometry.Lie.CotangentLieAlgebra` | 42 |
| `InfoGeometry.Geometry.CotangentUnitLinearization` | 26 |
| `InfoGeometry.Geometry.SkewGraphNeutralPairing` | 16 |
| `InfoGeometry.Geometry.MatrixDiracGraphs` | 24 |
| **Total** | **108** |

Every audited declaration is safe, non-partial, and not an axiom declaration. The exact transitive axiom union is **`Classical.choice`, `Quot.sound`, and `propext`**. All four new owners, the aggregate, and the audit were invoked with warnings treated as errors.

`InfoGeometry.All` has exactly the intended additional aggregate import and matches the index. The root `InfoGeometry` imports `InfoGeometry.All`; this confirms source routing, not a complete umbrella compilation.

## Evidence fingerprints

| Evidence | SHA-256 |
|---|---|
| `check-final/validation.json` | `54d8c6ad629bf56d4d4c1f453b320619e3b641b5e0f77dc04023c61893837e93` |
| Native audit log | `169bd3d496b467d8672e474930111e79127ed753c1d21c74b0fa6c6b58f00d74` |
| Final `MatrixDiracGraphs.lean` | `07fe9bfc4410845f7a763afc40cdda884a85a590230128e5ed4e91b6d03230d8` |
| `SEMANTIC_REVIEW.md` | `d8c751fa730db5cd4cee47dbb5ff481a518dcab8130abc47b2bcce1e60822e42` |
| Fresh staged-gate receipt | `7dacf5f8066641022820025753fdc879099d06137a805787e87d13d11a6c5087` |

All relative evidence paths are under `/workspace/scratch/3288f93e1961`; repository documents are under its `info-geometry-lean/verification/courant-dirac` directory.

## Documentation and fresh staged gate

The semantic receipt includes the final matrix proof reconciliation. The contract's claim ledger and all subsequent mathematical content are byte-identical to prior index blob `aeb4f09e`; only preceding intake/status wording changed. Its current and staged hash is `e959f5be12c9b26e5ac0e856b6db0e3dfa60590ff082a3864931c7e277078869`.

`check/logs/staged-gate-final.json` records **exit zero** and `proof_proxy_staged_gate: ok`. The gate and screener match baseline/index. Its 12-file inventory matches the reviewed set. All source/control hashes are unchanged. `VALIDATION.md` subsequently changed only to record the gate result and explain historical review notes: reversing those wording edits in memory reproduces the gate snapshot hash `82d3835b7e6d5e7aebe2a7ab1be78d995774e0f7993195e28f2ea4660ccc19ea` exactly. Its reviewed current hash is `8093c95faaa92778a683a7d582e43ef00e73a92368f5c6f45cc3756323028956`.

The final documentation line recording this QA outcome and the normal tracked pre-commit hook remain for the parent to record. Neither is silently included in this snapshot.

## Root-build boundary

The actual maintained root-build log, `check/logs/root-build.log`, records `lake build --wfail InfoGeometry.Geometry.CourantDrinfeldDiracCapstone` and **exit one while cloning Mathlib**, with `fatal: write error: No space left on device`. Owner compilation was not reached. The separately observed absent Atlas/HomotopyHypothesis paths and uninitialized pinned GIFT belong to the provenance preflight; they were not the observed cause of this invocation's failure.

The successful focused check used a separate provisioned exact-pin Mathlib checkout. This report certifies that narrower scope and makes no successful root-package, whole-umbrella, commit-hook, push-gate, or remote-publication claim.
