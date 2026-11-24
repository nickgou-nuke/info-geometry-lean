# Independent QA-A final acceptance review

## Disposition and exact scope

**Accepted for the stated algebraic scope.** The final dedicated CI run successfully built the seven mathematical owners and audit module, completed a separate fresh Lean axiom invocation, passed the strict source screen, and rebuilt the changed existing deep Cartan consumer. I independently retrieved the completed job log and actual artifact, verified the archive digest, parsed the untouched fresh axiom log, reran source checks, and checked source identity.

This acceptance covers the explicit 202-declaration inventory and the existing-consumer regression described below. It is not a whole-repository build certificate, a warning-free-build claim, or a proof of the smooth geometric interpretations excluded by the theorem contract. Earlier failed checkpoints are historical failures; this report supersedes their pending acceptance dispositions for the exact source state identified here.

I was a read-only reviewer of the mathematical owners and validation controls. I did not author theorem code, change proof or validation inputs, start local Lean/Lake, alter dependency pins, stop compiler processes, or mutate GitHub. My only local writes were review/evidence Markdown files under `candidates/triality_acceptance/`.

## Source and execution identity

| Item | Independently checked identity |
|---|---|
| Repository / PR | `nickgou-nuke/info-geometry-lean`, [PR #444](https://github.com/nickgou-nuke/info-geometry-lean/pull/444) |
| Base | `fe24e350b08fdea04f74c0748ef9fd9417c47529` |
| Verified remote proof head | `21816519e42b9f76a0c8004650c6b11a6024774f` |
| Matching local proof commit | `497c6d6664808e8ccb3082d6aabeba76dcd4e40a` |
| Exact common tree | `1c58b9eb55e126ebe8179702bdfec5e20bd73021` |
| Actual Actions merge checkout | `508e1557896790de0eb4be072b27bf2501070745` |
| Successful run | [45385261804](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45385261804) |
| Successful job | [138414407353](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45385261804/job/138414407353) |
| Execution date | 2026-11-24 |
| Lean | `4.34.1`, revision `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |

I fetched twelve source/control files directly at the verified remote proof head and compared their Git blob identities programmatically with the local proof commit. All twelve matched: the seven owners, audit module, changed existing consumer, dedicated workflow, `check.py`, and `audit.py`. The final working-tree check found no tracked changes to these proof inputs or focused package controls. Only validation prose and review records were pending at review time.

If a later publication commit adds only that prose, this report continues to identify the exact already-verified proof inputs. It does not represent a later documentation-triggered CI run as completed.

## Actual successful verification evidence

| Check | Observed result |
|---|---|
| Seven owners and audit-module build | Success, Lake exit 0; 3,298 jobs including dependency jobs |
| Separate fresh `env lean` audit invocation | Success, exit 0 |
| Fresh-log declaration coverage | Exactly 202 expected explicit public declarations, each once |
| Axioms in those declaration reports | Only `Classical.choice`, `Quot.sound`, `propext` |
| Workflow strict source screen | Success, zero traps |
| Existing `KreinCl44SplitG2DerivationPosetSynthesis` rebuild | Success, Lake exit 0; 9,048 jobs including dependency jobs |
| Source/configuration/runtime stability checks | Passed for build, fresh invocation, and regression |
| Evidence upload | Success; actual three-log artifact retrieved |
| Independent final source screen | Exit 0, zero traps |
| Independent final actual-log parsing | Exit 0, exact 202-record coverage and allowed axioms |
| Independent base-to-proof-head `git diff --check` | Exit 0 |

The Actions job counts are not counts of newly introduced sources. The reviewed canonical project import closure is 12 Lean files for the focused owners/audit and 134 with the deep consumer. The CI source/configuration snapshots include controls and dependency configuration as well: 53 files for the focused build/fresh invocation and 175 for the regression.

The focused build and fresh invocation used the same snapshot digest `be56d8ec0eec0d8f3fcb2520cf95ca6459e5fbd5d1039f9e6039b0da335cc75d`. The regression snapshot was `cc2715c1a00fc7455ab78f25d1b154b1ebcde43600c7a45915c58ebd8e371885`. Their before/after comparisons passed. These are stability checks for these executions; they are not a general reproducible-build theorem.

There are no Lean `error:` records in the successful raw logs. Earlier runs' elaboration failures and consequent `sorry` warnings are not used as positive proof evidence. No successful local native build is claimed: the parent’s local requests remained behind another task’s maintained lock and were cancelled while still waiting, before Lean/Lake started.

### Artifact provenance and independent axiom parsing

I independently used the GitHub artifact download capability for artifact [14916487441](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45385261804/artifacts/14916487441), named `triality-cotangent-validation`. I downloaded the ZIP into memory, verified its SHA-256 against the Actions digest, inspected its exact three entries, and read the fresh log without transformations.

ZIP SHA-256: `e5cf4cfe9ac3812b57bc21fe148be32dadb6a074a09229a506810bd541fa87fa`.

| Actual ZIP entry | Bytes | SHA-256 |
|---|---:|---|
| `triality-cotangent-build.log` | 42,794 | `103c99578b06cffa540a6742573e27f524e23bc29e222e76ab53e3eccae7750a` |
| `triality-cotangent-axioms.log` | 24,873 | `bb5a2be5a44178a5216cd9fb53e9a32ddbdf446c600e5a0c0e8297a6e8f1c084` |
| `triality-cotangent-regression.log` | 309,207 | `4081cf2437614089d755004bc3b6455b6a3b07b178ae3a8590ed14d72ceab698` |

I ran the maintained validator against the actual fresh log on stdin:

```text
python3 verification/triality-cotangent/audit.py --log /dev/stdin
Source coverage: 202 public declarations in 7 owners
Lean axiom audit passed; foundational axioms: ['Classical.choice', 'Quot.sound', 'propext']
exit 0
```

The parent separately downloaded and extracted the artifact. I verified that its three raw log hashes matched my independent extraction, then reran the validator against its raw file path with the same result. The exact fresh-log bytes and my parser result are retained in [ci6-fresh-axiom-evidence.md](ci6-fresh-axiom-evidence.md). Parsing the combined build-plus-fresh job transcript would be incorrect because the audit module emits records during both invocations; that combined transcript was not used for the acceptance parser.

The inventory counts explicit public source declarations, including named instances. It does not count compiler-generated projections, recursors, or auxiliary declarations as separate source declarations. The separate successful native build and the transitive axiom reports are necessary evidence beyond source-text enumeration.

### Warning classification

The introduced owners emit **six unique nonblocking style warnings**. There are **seven corresponding records** across the build and regression artifacts because the Cartan warning appears in both builds.

| Source location | Warning |
|---|---|
| `CotangentFixedShear.lean:34:41` | Unnecessary `<;>` sequencing |
| `CartanTriality.lean:323:25` | Unnecessary `<;>` sequencing; repeated in regression |
| `FiniteCotangentInvariants.lean:58:0` | Unused section hypothesis `[Fintype G]` in `invariantDual_action` |
| `FiniteCotangentInvariants.lean:127:0` | Unused section hypothesis `[Fintype G]` in `fixedCotangentForm_isAlt` |
| `FiniteCotangentInvariants.lean:165:0` | Unused section hypothesis `[Fintype G]` in `fixedCotangentLieForm_isAlt` |
| `FiniteCotangentInvariants.lean:68:4` | Unused `smul_smul` simp argument |

These warnings were not suppressed. The regression also emits warnings in existing owners. The zero-trap source-screen result must not be described as a warning-free Lean build.

## Validation-control review

I directly read the maintained checker, inventory/axiom parser, workflow, focused Lake configuration, README, and validation record, and inspected the final changes against earlier reviewed revisions. No validation bypass or false-success path was found for the advertised scope.

The checker uses canonical sources through `srcDir = "../../lean"`. It checks root/focused toolchain equality, all nine exact dependency pins, dependency checkout revisions and cleanliness, runtime Lean/Lake consistency, and source/configuration/runtime stability. It takes the maintained shared build lock, preserves lock ownership during cleanup, rejects unsuitable linked worktrees or package overrides, and propagates a failed Lake result. Cold dependency hydration is followed by exact revision and checkout validation; later checks include the hydrated configuration in their snapshots. No source copy or pin substitution is used.

The parser derives the explicit declaration inventory from the seven owners, rejects duplicate source names, verifies exact generated audit coverage, and requires each expected log record exactly once with only the three permitted foundational axioms. By itself, source parsing cannot establish a successful producer invocation. The workflow therefore uses `set -euo pipefail` and requires successful owner build and separate fresh Lean exits before the axiom parser can pass. It has no `continue-on-error` escape. The changed existing consumer is a separate required regression step.

The final independent source-screen command covered all seven owners plus the audit module. The actual-log validator, strict screen, and base-to-head diff check all returned exit 0 on the unchanged final proof input.

## Mathematical and integration review

I read the actual seven owners and the mathematical challenger's report, and inspected the repair diffs myself. The sources implement the following defensible algebraic claims:

- The generic coadjoint construction starts from an actual group representation and uses native action categories and groupoids. Raw composition carries the composability condition. The lift is a native equivalence, and the fixed subgroup/fixed-dual construction is an actual restricted groupoid. The inclusion is faithful with its precise fixed-label image; it does not assert unjustified fullness.
- The phase-space forms reuse the repository's neutral phase-space and contragredient pairing owners. The Lie form is bilinear, alternating, nondegenerate, and invariant under the stated Lie equivalence. The instance scopes correctly distinguish generic module data from native Lie algebra structures.
- The finite-action result uses native representation invariants and Reynolds averaging to prove the restriction/extension equivalence between invariant covectors and the dual of invariant vectors. The actual restricted phase-space form is nondegenerate. The proof does not insert an unstated finite-dimensionality premise.
- The explicit shear supplies the necessary counterexample to an arbitrary fixed-locus symplectic claim: fixed primal and dual directions pair to zero, and the nonzero fixed phase space has a degenerate restricted form.
- The Cartan owner proves the explicit matrix relations, coordinate conversion to the old convention, two-dimensional fixed-plane basis, and distinct cyclic orbit. Orthogonality is the actual coordinate inner-product identity; a Killing-form identification is not silently assumed.
- The native dihedral and permutation constructions give a faithful `S₃` representation, rather than only disconnected matrix identities. The final symbolic multiplication proof uses the proved order-three/reflection relations and native modular exponent APIs.
- The final specialization constructs the cotangent action groupoid for the actual additive four-dimensional vector group with its specified trivial adjoint representation. Its simultaneous fixed phase space is identified by a form-preserving equivalence with the cotangent space of the two-dimensional fixed plane. The four-dimensional result uses an actual transported product/dual basis and native `Module.finrank_eq_card_basis`.

The final basis repair changes proof implementation, not the theorem statement or hypotheses. I checked the basis-product, dual-basis, map directions, and finrank theorem against the pinned Mathlib source. Earlier repairs likewise do not supply new mathematical assumptions or weaken conclusions to obtain compilation. No custom axiom, proof hole, unsafe proof, or native-evaluation shortcut was introduced.

The old elementary Cartan block is extracted byte-for-byte into the new owner with its namespace preserved. The independently compared block is 5,435 bytes, SHA-256 `4accd6d59f1397005999062100d15ab0a046f9199829a646907f2ddffbd81ea2`, and occurs once in the new owner. The existing consumer's import/removal change is now supported by an actual successful regression build, rather than only textual comparison.

## Final mathematical source fingerprints

All paths below are under `lean/InfoGeometry/`.

| Path | SHA-256 |
|---|---|
| `Geometry/CotangentActionGroupoid.lean` | `5c87128ca8cb33fb142ca97ed1d9e4e1198e22c08a89057a7fe69d5579f183e8` |
| `Geometry/CotangentLieForm.lean` | `2c0baeda3c9030e1338c0e407956b71d8c82cbb10d0fd82bd2d3f15fcd135749` |
| `Geometry/FiniteCotangentInvariants.lean` | `119bc71961b2f7ec420fc59f9c85ae26f52c3b20e09fc7949047f38d2942f38c` |
| `Geometry/CotangentFixedShear.lean` | `05ff86257a14307c219d33ae6451d3185e5484ca4f4dd5f9205d42d9a8d8e062` |
| `Lie/CartanTriality.lean` | `6f37bbf035d2eaba74f0c9879069d67e6bb3d20ab67ac17a58ac77572d405f26` |
| `Lie/CartanTrialityRepresentation.lean` | `f46c49b533ed8f5a6bd037f3e3533dcaef486270555b9537d7daaf2d96bbd4ca` |
| `Lie/CartanTrialityCotangent.lean` | `5e411f959b1f150b65e4b2d3640e89f3dca831777b8d4e046ad0b664f848411d` |
| `Geometry/TrialityCotangentAudit.lean` | `96a4676afc831a986a82352f2fd7a2d360e33bd308e4647693e8260540b1d267` |

## Remaining boundaries

The accepted development is algebraic. It does not establish a smooth cotangent bundle, closedness or multiplicativity of a symplectic differential form, a Killing-form normalization, integration of these matrices to outer automorphisms of `Spin(4,4)`, or a smooth fixed `G₂(2)` subgroup. Those are explicit further obligations, not consequences of the completed matrix and action-groupoid proofs.

Other repository workflows have separate existing infrastructure or debt failures documented in [existing-ci-blockers.md](existing-ci-blockers.md), using their actual logs and base-to-PR path/blob comparisons. In particular, all 91 paths identified by the inspected initial sorry gate were outside the exact PR change set. This independent acceptance does not claim those other workflows passed, nor classify an uninspected later run by assumption.

**No blocking issue remains within this reviewed scope.** Publication may accurately cite the successful run, exact 202-declaration foundational axiom audit, zero-trap source screen, and successful existing-consumer regression, with the nonblocking style warnings and mathematical scope stated as above.
