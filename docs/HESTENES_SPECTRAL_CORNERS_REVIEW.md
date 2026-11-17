# Native Hestenes spectral-corner review

Review date: 2026-11-17. Baseline: `08c34e03f610b452e03422037949196dc7d92d6d`.

**Disposition:** the first hosted native run failed in an existing dependency before `HestenesSpectralCorners` compiled. Compiler-guided import and warning repairs have been independently reviewed; all five current scoped source checks pass. Fresh native compilation, target-warning acceptance, the compiled declaration-axiom audit, root-package pre-push acceptance, and repaired hosted CI acceptance remain outstanding. This is a draft publication, not a kernel-accepted completion claim.

## Current source identities

| Owner under `lean/InfoGeometry/Canonical/` | SHA-256 | Change |
|---|---|---|
| `HestenesSpectralCorners.lean` | `7d84d26877455cc6bad9f6b22e878b49a628d36307e4142fcca1a2361cf8501b` | New native projectors, involution/corner laws and a nonzero witness |
| `TwoSheetThreeColorWeylFinite.lean` | `f8c8c264e9920925aa01b6604a72a1e08654d4000c9cbf22d04a50d563d61b2b` | Remove one unused import, add the required header, and repair 20 actual target warnings without changing theorem statements |
| `HestenesEvenPauliEquiv.lean` | `9c5a6ef3a842909f81cbe6cfbfdfb971aae1c010aa3e37d2d09c277b76ed9c08` | Add the required direct Mathlib import and header; repair six actual warnings without changing theorem statements |

The four raw input hashes are recorded in the [contract](HESTENES_SPECTRAL_CORNERS_CONTRACT.md). Every preserved file matches its supplied local attachment byte-for-byte, including original trailing whitespace. The third input has an original blank line at EOF; it is preserved as provenance. Code and authored-document whitespace are checked separately.

## Reuse and scope decision

The initial source audit prepared an overlapping real uncertainty candidate. A subsequent current GitHub search found open PR #372 and its stacked PR #379, and actual source inspection confirmed that they already supply the centered commutator, real uncertainty, normalization interfaces and proposed native right-phase specialization. The overlapping candidate and its competing area-proof extraction were not promoted. This branch changes no uncertainty owner and is based directly on main.

The native spectral-corner result remains distinct: it concerns the even boost bivector `β=γ₁γ₀`, complementary projectors, bare reversion versus the fixed-observer adjoint, and a nonzero obstruction to the claimed corner exchange. The contract links the exact related revisions without treating their draft source as accepted native evidence.

## Independent semantic review

The candidate was independently reviewed against the actual `Q14`/`ClPlus14` definitions, generator relations, reversion and Hestenes adjoint owners. The carrier is the full eight-dimensional real even Clifford algebra. All four generic corner statements quantify over arbitrary `x : ClPlus14` and preserve ordered multiplication.

Review confirmed that reversion exchanges the projectors and reverses product order, hence preserves each off-diagonal corner. The fixed-observer adjoint fixes the projectors and exchanges the corners. The transverse witness is genuinely nonzero and square-zero; its reversed value is nonzero while its opposite-corner compression vanishes. The matrix-entry calculation is used only to separate the native projector from zero.

One likely redundant final tactic in the transverse anticommutation proof was removed during integration. The new file closes its unnamed noncomputable section with `end` and describes the chosen observer as fixed. No theorem statement was weakened. A follow-up static proof review removed three redundant simp arguments in the two orthogonality proofs and transverse-square proof. These are source-review predictions, not diagnostics from the previously blocked corner owner; the next native run must check them.

Two independent source reviews checked the complete finite-sheet owner and its direct consumers before removing the unused `ChiralCausalCone` import. Its remaining imports supply its carriers, native matrix/Kronecker API and tactics. Both aggregate consumers explicitly retain the historical lane; neither direct Hestenes consumer uses it. The import trim introduces no stub or replacement declaration.

The native failure artifact was independently downloaded, SHA-256 checked, and reconciled against all 11 archived/live source files. Review of the pinned Mathlib source identifies the missing direct import precisely. No source reviewer claims a successful compilation of the repaired candidate or its compiled axioms.

## Actual scoped source results

The fresh receipt is `/workspace/scratch/a6c715447467/verification/hestenes-spectral-repair-final-source/receipt.json`. It records the current hashes and all five commands:

| Check | Observed result | Coverage |
|---|---|---|
| Strict placeholder audit on `HestenesSpectralCorners` | Exit `0`; one file scanned; zero hard/soft findings | The new owner |
| Strict placeholder audit on `TwoSheetThreeColorWeylFinite` | Exit `0`; one file scanned; zero hard findings; six soft findings | The import-trimmed owner |
| Strict placeholder audit on `HestenesEvenPauliEquiv` | Exit `0`; one file scanned; zero hard/soft findings | The import-repaired owner |
| Semantic-vacuity gate with `--fail-on error` | Exit `0`; all three files selected and read; complete coverage; zero errors; two warnings | All three selected owners |
| Strict OpenGauss screener | Exit `0`; no violations or quarantine packets | All three selected owners |

The six placeholder soft findings all concern unchanged finite-sheet source: the five short algebraic proofs `omega_sum`, `omega_mul_three`, `omega_mul_square`, `omega_square_mul`, `sheet_projector_parity`, and the visible cyclotomic section hypothesis. The semantic warnings are the existing `M2C` and `M3C` aliases of full matrix carriers. Their content was inspected; they are not proof holes or assumed corner conclusions. Findings remain visible, and the thresholds are unchanged.

These are lexical/source checks. They do not certify compiled axiom dependencies or successful Lean elaboration.

## Dependency and workflow review

The actual maintained closure resolver succeeds with:

- Three native targets: `InfoGeometry.Canonical.HestenesSpectralCorners`, `InfoGeometry.Canonical.TwoSheetThreeColorWeylFinite`, and `InfoGeometry.Canonical.HestenesEvenPauliEquiv`.
- Eleven repository modules in total, including eight other dependencies.
- Fourteen direct Mathlib import roots, with no unresolved `Architect` or historical `proofs.*` imports.

The workflow is [hestenes-spectral-corners.yml](../.github/workflows/hestenes-spectral-corners.yml), SHA-256 `1ec62574fb0945c2c94ed36c34b324ed3eac9d243c68a629e7dd28767f77bf8d`. Candidate YAML parsing, seven `bash -n` checks, and five Python `ast.parse` checks passed. The repair expands the previously reviewed workflow consistently to all three edited owners. Every target-derived audit and both target-count assertions use this same scope, with no source-only exception.

The workflow uses the unchanged maintained native checker, closure resolver, native declaration auditor and shared lock. It checks the exact public event SHA and unchanged Lean `v4.34.1` / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins. It requires fresh compilation of every resolved repository module, no reused project outputs, zero warnings on all three targets, and native enumeration of every declaration owned by them. The only permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`; unsafe and partial declarations are rejected.

All three owners receive strict source checks and complete coverage reconciliation. The evidence binds live/copied source hashes, 20 named verifier/provenance inputs, the two documents, all four raw inputs and resulting reports. Counts are computed from the actual closure. Evidence is uploaded even on failure. Workflow source and syntax review do not mean that GitHub Actions has succeeded.

## Actual first hosted failure and its repair

[Run 44056529125](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44056529125), job `133947229684`, failed in the native closure stage at published head `c3fe3d8c74e4d26d632ce5262daff2f7a6687e56`. Checkout, pinned environment, and cache acquisition succeeded. The exact errors were an unknown `Complex.finrank_real_complex`, an unresolved real matrix dimension equation, and a missing `FiniteDimensional ℝ Sheet` instance in `HestenesEvenPauliEquiv`. `HestenesKreinMatrixBridge`, `HestenesHermitianAdjoint`, and `HestenesSpectralCorners` were consequently blocked; the new corner owner did not compile. The axiom audit and subsequent source/hash stages did not run.

The artifact is `14318479669`, SHA-256 `f59faa7bb60ee2b26456fce45d12732fff94b184db65329e431fadf920b10bcd`. Its 11 archived source hashes were independently matched to the corresponding published sources. The run recorded 20 warnings in `TwoSheetThreeColorWeylFinite`, six in `HestenesEvenPauliEquiv`, and 46 in unchanged dependency owners. The two edited owners now have targeted tactic repairs; no linter is disabled. Dependency warnings are not represented as target acceptance.

The old sheet SHA-256 was `0809bcad8e719f75521aeaf450ac7515160d2354a368afd4402d38f2ef6e8274`; the old equivalence SHA-256 was `ea46cc8d2affcba549686b874259d63142a03771f4d885349677c3278b97dc54`. The repaired hashes appear in the current identity table. No successful result from old bytes is transferred to the repaired sources.

## Native and publication gates

Tracked hooks are installed in an independent checkout. The actual normal commit hook passed on the selected source checkpoint with `proof_proxy_staged_gate: ok`. This is a staged source result, not native acceptance. Actual local/hosted native receipts and the root pre-push result must be reported separately at their precise source revision.

The earlier broader local checker was stopped with exit `130` while still waiting for the shared lock, after remote overlap made its unpublished uncertainty work redundant. It had started no compiler. The external lock holder and its build were untouched. The repaired native check uses the same maintained checker and lock with all three target arguments above; a wait or an empty output directory is not a successful check. A fresh nonblocking availability probe observed the shared lock still held by another native build, so it is not bypassed or replaced. Hosted execution provides an independent fresh runner.

No successful full root-package build, `src/`-lane check, acceptance of the related PRs, or PDE/QFT conclusion is claimed. The mathematical and interpretation boundaries remain those in the [contract](HESTENES_SPECTRAL_CORNERS_CONTRACT.md) regardless of a later compiler result.
