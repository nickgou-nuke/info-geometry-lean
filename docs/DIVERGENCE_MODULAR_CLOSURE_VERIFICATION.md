# Verification of the finite divergence and modular connections

## Accepted source and scope

Independent A-A review passed. Independent QA-A returned
`ACCEPTED_WITH_LIMITED_SCOPE` on 2026-11-19 for the nine owners listed below.
The accepted mathematical scope is the finite positive-distribution calculus,
scalar exponential family, centered real Gaussian covariance evaluation, and
full finite relative-modular/CFC connection described in the
[theorem contract](DIVERGENCE_MODULAR_CLOSURE_CONTRACT.md).

The accepted sources were staged over local base
`d759fdc9e9a27806b66c1167c03e40d5c307c6ec`; the staged tree before adding this
verification document was `18250e4fa54ba2e1d3216e18fab4d2836e7a97ce`.
That local base has exactly the same tree as upstream PR #410 head
`abc8365b24c3ba6292fba3a83a8d36a99903bd84`.
The native report records the local base revision and separately hashes the
actual changed working sources. It does not pretend those edits were already
part of the base commit.

Current working files, staged blobs, the fresh compiler snapshots, the QA
preflight, and the final A-A source hashes reconciled with zero mismatches.
Later documentation and commit metadata do not change the accepted Lean,
workflow, dependency, or checker bytes. The PR body records the final
published Git tree; upstream CI results are added only after the corresponding
exact-head run has been observed.

Generation, semantic review, and acceptance used separate contexts. The A-A
reviewer did not author or compile the proofs. QA-A did not edit repository
sources. The parent integrated candidate proofs and the Gaussian/Stein and
generalized Gibbs consumers.

## Fresh native kernel check

The final QA command was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/85b0f1eb27b8/lean_verification_runtime/mathlib4 \
  --lean /workspace/scratch/85b0f1eb27b8/lean_verification_runtime/lean-4.34.1/bin/lean \
  --output /workspace/scratch/0b027a897d29/divergence-closure-verification/qa-final-r2 \
  --target InfoGeometry.Jordan.BurgStein \
  --target InfoGeometry.Probability.KullbackLeiblerProduct \
  --target InfoGeometry.Probability.GaussianKullbackLeibler \
  --target InfoGeometry.Probability.GaussianTraceLogdet \
  --target InfoGeometry.InformationGeometry.PositiveMeasureDifferential \
  --target InfoGeometry.ExponentialFamily.FiniteAnalyticKL \
  --target InfoGeometry.Canonical.MatrixRelativeModular \
  --target InfoGeometry.Canonical.MatrixRelativeModularPhysicsBridge \
  --target InfoGeometry.Canonical.GaussianBurgStein
```

The command exited zero. It used neither `--incremental` nor `--skip-audit`.
All **42 repository modules** in the dynamically resolved source closure
compiled freshly; **zero repository artifacts were reused**. All **nine
selected owners had zero compiler warnings**. The 29 warnings in ten
unchanged prerequisite owners were retained in the report.

| Selected owner | All owned declarations audited |
|---|---:|
| `Jordan.BurgStein` | 40 |
| `Probability.KullbackLeiblerProduct` | 7 |
| `Probability.GaussianKullbackLeibler` | 7 |
| `Probability.GaussianTraceLogdet` | 4 |
| `InformationGeometry.PositiveMeasureDifferential` | 20 |
| `ExponentialFamily.FiniteAnalyticKL` | 9 |
| `Canonical.MatrixRelativeModular` | 65 |
| `Canonical.MatrixRelativeModularPhysicsBridge` | 6 |
| `Canonical.GaussianBurgStein` | 15 |
| Total | **173** |

The native audit covers private and generated declarations as well as public
definitions and theorems. It recursively collects their dependency axioms and
allows only `propext`, `Classical.choice`, and `Quot.sound`.
No other axiom was found. This count is an audit count, not a count of 173 new
substantive theorems.

The runtime remained Lean 4.34.1, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, with Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
Mathlib sources and all dependency pins were unchanged.

## Static checks and reviewed heuristic findings

The final strict OpenGauss source screen and refutation check exited zero.
The explicit use of the Gaussian variance-nonzero premise replaced an
implicit use through `positivity`; no hypothesis or conclusion was changed.

Gate 4 source preflight, the scoped style audit, lexical axiom-debt checks,
strict placeholder scans, and staged whitespace checks passed. Gate 4 is
a static preflight, not a kernel certificate. After the correction, its
three changed Probability owners were checked again; previous successful
results were retained only for the six byte-identical owners, with their
original log hashes. Each fresh Gate 4 invocation also runs the full current
staged-index proof preflight.

The workflow YAML, its Bash bodies, and all three embedded Python blocks
parsed. Its nine targets, all 42 source-closure trigger paths, and the four
terminal `InfoGeometry.All` registrations were checked. This is registration
validation; the whole `InfoGeometry.All` aggregate was not compiled.

**The warning-strict semantic-vacuity command returned exit 1.**
It reported eight `trivial_surface` warnings. Independent A-A review
adjudicated all eight as legitimate representation, linearity, or
determinant-one normalization lemmas. The detector's own category explicitly
allows valid definitional lemmas to receive this warning and calls for owner
review. The raw exit code is retained, not relabeled as a clean pass.

The strict placeholder scans returned zero, with **zero hard findings,
zero advisory findings, and seven SOFT `skeletal-proof` findings**. These
seven heuristic findings were also independently adjudicated. Six overlap
with the eight semantic warnings, so nine distinct declarations were reviewed:

| Declaration | Independent disposition |
|---|---|
| `normalizedDistortion_shapeCovariance` | Native matrix scalar multiplication identifies the constructed scaled SPD covariance with the relative shape; consumed by the shape loss and trace-bound proofs. |
| `squareRootExpectation_sub` | Native matrix/vector linearity; applied twice in the general modular IS trace-correction proof. |
| `familyLogPartition_eq_logSumExp` | Honest equality of the actual two function definitions; consumed by the genuine first- and second-derivative theorems. |
| `steinLoss_eq_trace_minus_logdet_minus_dim` | The inherited public unfolding equation, unchanged from the base and exported by the existing canonical logdet owner. |
| `trace_relativeShape` | Native trace linearity for the scaled relative matrix; a valid calculation API with no current named consumer found in the bounded search. |
| `relativeScale_eq_one_of_det_eq_one` | Uses the actual determinant-one hypothesis, `log 1 = 0`, and `exp 0 = 1`; feeds the next normalization corollary. |
| `relativeShape_eq_distortion_of_det_eq_one` | Valid specialization of the constructed shape to determinant one; no external named consumer found. |
| `steinLoss_eq_trace_sub_dim_of_det_eq_one` | Removes the actual logarithmic determinant term under an explicit determinant-one condition; it does not assert zero shape cost. |
| Private `hasDerivAt_affine` | Complete native derivative proof from identity, multiplication by a constant, and addition of a constant; consumed throughout the affine Hessian and positive-neighborhood proofs. |

The determinant-one hypotheses are nonvacuous. For example,
`X = diag(2, 1/2)`, `Y = I` has determinant-one relative shape and Stein
loss `1/2`. Short normalization proofs do not collapse this shape slice to
identical states. No proof padding, tactic obfuscation, or checker changes
were used to silence the heuristic observations.

## Source fingerprints

| Selected owner | SHA-256 |
|---|---|
| `Jordan.BurgStein` | `391e1cd6d7fe821c9b63281cb866568af6138808f3192eb267538ebd7a49e6f9` |
| `Probability.KullbackLeiblerProduct` | `0c9d6962a0e8098076aa862d388153766a251db81e75b20ff2d985b0d9771c3d` |
| `Probability.GaussianKullbackLeibler` | `242e34c46904c05b6961aa712613230607d184728ec719e96504900ba3f724fb` |
| `Probability.GaussianTraceLogdet` | `4527328936c7398494c4975797a2641fef2d0105046acd74cce260b9a8ab4b8f` |
| `InformationGeometry.PositiveMeasureDifferential` | `4bdb1a0eb3366d7a09b939cfbd9a638fef097081a54b7ed3326f024c3d6ea26a` |
| `ExponentialFamily.FiniteAnalyticKL` | `5c854c0b81c26004d7ff532666618d38a87f286874234c39dd0819d29db2e2dd` |
| `Canonical.MatrixRelativeModular` | `e8e2bb7d345dbd22ae8865d7af50ebf6e0e4dcb15d444967fcffb7e9520951f8` |
| `Canonical.MatrixRelativeModularPhysicsBridge` | `cf5b18d4466ebaa97d1405960cbe638328be05df82cc6f16a8fb9c091af3b697` |
| `Canonical.GaussianBurgStein` | `afbfea7e79710c4944548374b3eb4dfc9602edd003fdbbc62c9144ea8920b03a` |

The scoped workflow SHA-256 is
`3e571d849e7257efbb759d4e2ac4c4d4907fa05d374ea07759f9113a000b964a`.

The maintained verification helpers are unchanged from the base:

| Helper | SHA-256 |
|---|---|
| `tools/quality/check_clifford_dirac.py` | `fcf6fbb9845e0ee2a85bdb3778c5fe74345a9ae7a2e97e871d0a89d3e98e7db0` |
| `tools/quality/check_reviewed_prs.py` | `ddcd656bf93db21238748a1fef6d1a557f5ac3289eb439299fda3088deac19ba` |
| `tools/quality/reviewed_audit_source.py` | `a976c910f5efb4611b1626d714e3197310d92648ffae56513e94a49ae5f0f206` |
| `tools/build_lock.py` | `02e3e6712a2f1b716965e49ab8f7e0f0bbaf5b528d7ad723496fd373af7401df` |

Evidence fingerprints from the independent acceptance run:

| Record | SHA-256 |
|---|---|
| Native compiler report | `446bce972174446f8513617f4159f259f7339e91b755976d6846382578cdb3e5` |
| Native declaration/axiom output | `c2077d1102e2444e727dc0b47a518eada5f70462eb2bb6201d4d15ed8d079384` |
| QA-A acceptance JSON | `1dfe1648f09b82941df6b57b78a77f256d0baf2c43a7504fa2ac7709844b38d6` |
| QA-A acceptance report | `f6a2a87e7a1804499ea5429f6724b0620c1e31e2293e44790f2cb2f2ceeec309` |
| QA-A evidence manifest | `7c72dae11c6633b122fb173f99f7be6d3faf27097e5819439205a28f678e11f1` |
| Final A-A semantic review | `ebc9883bb9ca1e79caf0f773e9cec41d3790f88d66df628ebf4a67be31e3ceec` |
| A-A heuristic adjudication | `d2a22dc442ba69d6cd172b29c35877cd0b87b28c9833cb16a3ad7e0043fd65a2` |
| A-A source-hash record | `d78d32355e15097409306553dedcc0a8c3f2c8ed0692e6435637a624cff47415` |

These identify the local evidence. The
[scoped workflow](../.github/workflows/divergence-modular-closure.yml)
independently compiles the exact published head and uploads its reports,
logs, source snapshots, runtime/dependency provenance, and evidence hashes.

## Separate root integration condition

The maintained root Lake wrapper was executed against
`lean/InfoGeometry/Canonical/MatrixRelativeModularPhysicsBridge.lean`
with the pinned Lake executable and the shared build lock. It exited 1 during
dependency resolution:

```text
HomotopyHypothesis: package directory not found:
external_refs/homotopy-hypothesis-lean4
```

Its log SHA-256 is
`6d1303a3495fdd992893fe3e79cbad7209bedac176585c7075461b09ecab3462`.
The prior initial lock-contention attempt was retained separately and was not
treated as a build result.

The HomotopyHypothesis and Atlas path packages have no reconstructible Git
revision in the manifest. The GIFT core path is a pinned Git submodule.
No replacement package, invented pin, stub proof, destructive cache repair,
or weakened root/checker gate was introduced.

This is scoped mathematical acceptance. It does not establish a root Lake
build, compilation of the whole All aggregate, Type III standard form,
a physical heat-cycle protocol, or a spacetime/graded-scale identification.

## Installed publication hooks

The installed pre-commit hook accepted implementation commit
`61fd231bc6e0ccc5f4abb5b611bff7bc323b8779`, tree
`6cefd3c92e5336d87e59469f8c531da2241f3574`.
The actual installed pre-push hook was then invoked for that exact checked-out
commit and a new remote branch, using the real hook stdin record:

```text
refs/heads/codex/divergence-modular-closure-20261119 61fd231bc6e0ccc5f4abb5b611bff7bc323b8779 refs/heads/codex/divergence-modular-closure-20261119 0000000000000000000000000000000000000000
```

```bash
bash .githooks/pre-push origin https://github.com/nickgou-nuke/info-geometry-lean.git
```

The invocation ran from 2026-11-19 14:38:28 UTC to 14:41:46 UTC and
**returned exit 1**. It classified the branch's full ancestry range from
`origin/main`'s merge base `08c34e03f610b452e03422037949196dc7d92d6d`.
Its locked Lake build again failed during resolution of the missing
HomotopyHypothesis path package. The subsequent 17-file lexical axiom/debt
audit, 27,290-file semantic-content scan, tracked Lean scope audit, and
quarantine audit all passed their respective gates. Historical quarantine
debt remains visible in the latter reports; those passing gates do not turn
it into proved source.

Because the ancestry-range gate failed, the hook did not reach its later
root-package invocation. This is a failed publication-gate result, not a
successful root build. The log SHA-256 is
`b570cd9558bfeb8d0b0bbb4d72045154d4d9cd2ed5f803c3f795f18c743365ae`.

This documentation-only follow-up records the observed hook result without
changing the accepted Lean owners, workflow, verification helpers, or pins.
The draft PR is published for upstream review at the user's explicit request,
with the root integration failure disclosed and no merge performed.
