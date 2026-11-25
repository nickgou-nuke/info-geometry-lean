# Independent QA-A validation checkpoint

## Disposition

**Not accepted at this checkpoint.** The first dedicated CI run fails in introduced Lean owners. No successful fresh declaration/axiom run or existing-consumer regression has yet been observed.

This report is an independent validation review; it is not a theorem-author report and it makes no whole-repository build claim.

## Source and remote identity

- Repository: `nickgou-nuke/info-geometry-lean`, PR [#444](https://github.com/nickgou-nuke/info-geometry-lean/pull/444).
- Base: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
- Local candidate: `168eeb1cbb898541ed43e46b016b22525e6397b0`.
- PR head inspected in the checkout log: `501523dba3ec6e433e1d63b30b47f0cf9172099b`.
- Actual Actions checkout: merge `325da1357566a30085ebb3a407ca98a2d26cc3e1` of that head into that base.
- The fetched PR patch lists the same 18 files as the local base-to-head comparison.
- Seven owner file hashes independently recomputed and found in the mathematical challenger's actual final-source review. Explicit declaration count is 202.

## Validation-control source audit

I directly read `check.py`, `audit.py`, the focused Lake configuration, workflow, README, and validation record. The control design is adequate for the advertised focused scope:

- Canonical sources are used through `srcDir = "../../lean"`; no copied proof sources or dependency-version substitutions are used.
- Root and focused pins, nine dependency revisions, complete tracked checkout cleanliness, runtime Lean/Lake identity and consistency, and source/configuration before/after hashes are checked.
- The maintained shared build lock is actually acquired; child cleanup preserves lock ownership. No competing local Lean job was started by this reviewer.
- Explicit public source declarations are enumerated, duplicate names rejected, and the generated audit checked for exact coverage.
- Axiom-log validation requires each declaration exactly once and permits only `propext`, `Classical.choice`, and `Quot.sound`.
- Workflow `set -euo pipefail` requires a successful owner build and a successful fresh `lean` audit invocation before log acceptance. The source checker cannot stand in for those exits.
- The changed existing Cartan consumer is an explicit, separately executed regression target. The isolated package does not claim a full-repository build.

No present control bypass or false success path was found. Before/after hashes establish stability during each command, not a universal reproducible-build theorem. The cold-cache command validates newly created dependencies by exact revision and checkout cleanliness after hydration; the subsequent focused build also snapshots their configuration files.

## Independently executed source checks

1. `python3 verification/triality-cotangent/audit.py`: exit 0; `Source coverage: 202 public declarations in 7 owners`.
2. `python3 tools/infra/opengauss_screener.py --strict` on the seven mathematical owners and `TrialityCotangentAudit.lean`: exit 0; 0 traps detected.
3. Recomputed seven source SHA-256 values, compared them to the actual independent mathematical review, and verified the generated audit text equals the source-derived inventory.

These are source checks only. They do not show elaboration, kernel acceptance, or absence of transitive nonfoundational axioms.

## Independently retrieved CI evidence

- Run [45370890807](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45370890807).
- Job [138364561788](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45370890807/job/138364561788).
- Setup, pinned toolchain installation, and pinned Mathlib artifact restoration: success.
- Build/fresh-axioms step: failure at owner build, Lake exit 1.
- Runtime in the actual job: Lean 4.34.1, revision `5045d0056413266e57c625dcd7c365b10e377c52`.
- Source/configuration/runtime stability checks: passed even after build failure, correctly without turning failure into success.
- Source-screen and existing-consumer-regression workflow steps: skipped because build failed.
- Evidence upload: success; artifact `14907869239`, one build log, ZIP SHA-256 `5cd26402671ec5f323429d09d59e70dcf03d6e83bd666a5d8826f3d11d5eae3d`.

All 27 Lean error records are in newly introduced owners, not preexisting unrelated targets. The errors include incompatible inherited typeclass structures in the Lie form, native action-category instance reduction issues and rewrites, and finite vector simplification in new Cartan declarations. The source files contain no explicit `sorry`; the downstream compiler warnings about declarations using `sorry` follow failed elaboration and must not be confused with a successful kernel audit.

```text
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:63:29: `simp` made no progress
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:64:19: unsolved goals
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:65:14: unsolved goals
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:66:15: unsolved goals
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:84:79: unsolved goals
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:91:26: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:102:6: Type mismatch: After simplification, term
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:107:6: Type mismatch: After simplification, term
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:128:50: Application type mismatch: The argument
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:128:19: synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
error: ../../lean/InfoGeometry/Geometry/CotangentLieForm.lean:129:57: Application type mismatch: The argument
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:81:8: (kernel) declaration type mismatch, 'InfoGeometry.Geometry.CotangentActionGroupoid.cotangentGroupoid._aux_1' has type
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:81:8: (kernel) declaration type mismatch, 'InfoGeometry.Geometry.CotangentActionGroupoid.cotangentGroupoid._proof_3' has type
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:81:8: (kernel) declaration type mismatch, 'InfoGeometry.Geometry.CotangentActionGroupoid.cotangentGroupoid._proof_4' has type
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:274:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:301:10: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:314:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:375:40: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:395:8: (kernel) declaration type mismatch, 'InfoGeometry.Geometry.CotangentActionGroupoid.fixedGroupoid._aux_1' has type
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:395:8: (kernel) declaration type mismatch, 'InfoGeometry.Geometry.CotangentActionGroupoid.fixedGroupoid._proof_3' has type
error: ../../lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean:395:8: (kernel) declaration type mismatch, 'InfoGeometry.Geometry.CotangentActionGroupoid.fixedGroupoid._proof_4' has type
error: ../../lean/InfoGeometry/Lie/CartanTriality.lean:314:54: linarith failed to find a contradiction
error: ../../lean/InfoGeometry/Lie/CartanTriality.lean:314:54: linarith failed to find a contradiction
error: ../../lean/InfoGeometry/Lie/CartanTriality.lean:314:54: linarith failed to find a contradiction
error: ../../lean/InfoGeometry/Lie/CartanTriality.lean:314:54: linarith failed to find a contradiction
error: ../../lean/InfoGeometry/Lie/CartanTriality.lean:351:27: linarith failed to find a contradiction
error: ../../lean/InfoGeometry/Lie/CartanTriality.lean:353:20: linarith failed to find a contradiction
```

The Actions cleanup also warns about the existing `external_ref/open-math-harness` submodule URL metadata. That is a post-job warning; it did not cause the owner build failure above.

## Required next acceptance evidence

A repaired final source state needs a successful dedicated owner build, a fresh successful Lean invocation producing exact 202-declaration (or explicitly updated) axiom coverage, independent re-parsing of that actual log, source screens on the final files, and the existing-consumer regression result. Final source/head identity must be re-recorded; current report is not approval to merge.

