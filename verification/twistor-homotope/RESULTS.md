# Ordered homotope and twistor invariant verification

## Independent focused acceptance passed

Disposition: **`FOCUSED_HOSTED_QA_ACCEPTED`**.

The complete focused verification passed, and an independent non-authoring
QA reviewer initiated and inspected a second execution of the same frozen
source. Both executions passed all 15 recorded commands and their result
checks. The immutable [acceptance receipt](HOSTED_QA_RECEIPT.json) and its
[checksum](HOSTED_QA_RECEIPT.json.sha256) preserve the exact scope and evidence.

Receipt SHA256: `6da5670934c47c854510fedbfc004e2044f7661723e060ac805c27cd8246aa44`.

This is acceptance of the six mathematical owners, their declaration audit,
and the focused verification procedure. It is not a whole-repository build,
style, integration, or physical-classification certificate.

The [evidence index](HOSTED_QA_EVIDENCE_INDEX.json) records 77 retained evidence files. Its SHA256 is
`17650c4a605620afbbd651b033c912b4a76812ffe4e7f0e60c0e55084aef5175`.

## Verified source and environment

| Item | Identity |
| --- | --- |
| Published frozen head | `77b573e3bb12de62fef132cdc2ee63ef19fbfa4c` |
| Exact frozen tree | `0dff69f32d4ed42bafbb4fe975229751a6f8a6c3` |
| Hosted merge checkout | `1b88340e467907ffcbb8d5f7295e285f16838c7e` |
| Local checkpoint with the same tree | `bf6517f231ddb30ba3abdbcfee27c3c822a782ea` |
| Implementation base | `c143c264bc18bbf41d692be4e270b5b7f7405702` |
| Lean | `leanprover/lean4:v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |

The hosted merge has the recorded base and published head as parents. All
mathematical source is identical to the source that first passed the complete
build and fresh audit in run `43030148810`. The later verification revision
added the reviewed heuristic classifications and retained review evidence.

## Executed evidence

- [Initial complete pass](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43032133481/job/130561597286), run `43032133481`, attempt 1.
- [Independently initiated rerun](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43032133481/job/130565234717), attempt 2.
- [Initial artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43032133481/artifacts/13862475703), ZIP SHA256 `5b631e0d802b2fee0cfe27c7cd220b073ed00b52dae19f180efbfa43e62f480b`.
- [Independent artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43032133481/artifacts/13861757275), ZIP SHA256 `38970e6708ae415b494ee691fbe80f60a512cb441980511acd5e14cb29539b92`.
- Independent `checks.json` SHA256: `b567b85202a1c672090cb5ccf95be07c1d0f39b6f82eea12f6d63d5f9b1b44c7`.

The independent rerun restored the build cache, performed its Lake build,
and separately executed a fresh Lean declaration audit. It is not described
as a cache-free rebuild. Its build reported 3316 jobs; the original complete
build reported 3322. These are Lake task counts, not theorem counts.

| Check | Actual result in both complete passes |
| --- | --- |
| Focused Lean build | PASS |
| Separate fresh declaration/axiom audit | PASS |
| All named source theorems under their actual owners | 70 present, including six private helpers |
| Strict OpenGauss screen | No violations |
| Strict refute | Six mathematical files, all PASS and clean |
| Static Gate 4 | Seven files, no trap or scope findings; explicitly `kernel_checked = false` |
| Regex vacuity scans | All seven executed; two exact source-reviewed false positives, five empty results |
| Scoped whitespace | PASS |
| Protected-source equality and invariance | PASS against committed bytes |
| Root controls | 15 unchanged from the implementation base and invariant during verification |
| Dependency source state | Nine exact pinned Git packages, clean and invariant |
| Compiled artifacts | SHA256 recorded for seven `.olean` and seven `.ilean` files |

Static Gate 4 does not itself claim kernel verification. The separate Lean
build and fresh declaration audit supply that evidence. Its staged-hook
invocation on a clean CI index also does not reproduce changed-source hook
coverage. The actual tracked pre-commit hook and staged whitespace check ran
and passed on the source repair commits; the report keeps those observations
separate from the hosted per-file source checks.

Four nonblocking diagnostics remain in the new owners: one unused simp
argument and three no-op `push_cast` hints. Neither execution used
warnings-as-errors. These hints and the 23 inherited dependency warnings
are recorded in the receipt.

## Declaration inventory

The fresh audit enumerates actual owning modules, including private and
generated kernel-visible declarations. It found **116 declarations**:
**99 theorem declarations**, comprising **70 named source theorems** and
**29 additional generated theorem declarations**, plus **17 non-theorem
declarations**. The source inventory includes 64 public and six private
theorem declarations.

| Mathematical owner | Named source theorems | Runtime declarations |
| --- | ---: | ---: |
| `OperatorAlgebra.OrderedHomotope` | 15 | 24 |
| `Algebra.TwoModeCountRecurrence` | 14 | 35 |
| `Twistor.ConstituentWittGram` | 22 | 32 |
| `Twistor.ConstituentCayleyGram` | 16 | 19 |
| `Twistor.ConstituentInvariantIndependence` | 2 | 5 |
| `Twistor.MomentHomotopeWitness` | 1 | 1 |
| **Total** | **70** | **116** |

Only `propext`, `Classical.choice`, and `Quot.sound` occur as permitted
transitive foundational axioms. The audit accepted no introduced axioms or
unsafe/partial declarations in the mathematical owners. The full name and
axiom-membership records are retained in the receipt and raw audit outputs.

## Reviewed heuristic findings and repair history

The vacuity checker is a regex heuristic. It emitted `no_hyp_use` for the
binder strings `T X Y ` and `n `. The homotope proofs use their elements
through the goal; the recurrence bounds explicitly instantiate their prior
lemmas at `n`. The textual heuristic does not model that proof dependence.

[VACUITY_REVIEW.json](VACUITY_REVIEW.json) records the exact finding arrays,
source hashes, linter hash, and mathematical explanations. The driver retains
every raw result and permits only those exact reviewed parameter-occurrence
findings. Every different or unreviewed finding fails. The recurrence case,
initially recorded as conditional, was actually observed and matched in both
complete executions. This classification does not apply to holes, `True`
substitutions, assumed conclusions, or circular proofs.

The five checksummed `A_A_*_REVIEW.json` records preserve the independent
source review and its deltas. Actual compiler diagnostics led to the pinned
matrix-notation import and explicit conjugation normal forms. Marking the
recurrence `noncomputable` suppresses Lean's generated executable
`counts._unsafe_rec` helper while retaining its safe kernel definition,
equations, and proofs. The audit's rejection rules remained unchanged.
Earlier failed runs remain failed evidence; they are not relabelled as passes.

## Repository integration boundary

The broader repository workflows still expose issues outside this change:

- [Root CI](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43032133393/job/130561655023) reports missing `homotopy-hypothesis-lean4` and `atlas-lean` path packages and an uninitialized GIFT gitlink.
- [Repository style lint](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43032133411/job/130561596959) stops at the existing `PellisFineStructure.lean` / `PellisfineStructure.lean` case collision.
- [Repository debt audit](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43032133689/job/130561598066) reports 878 forensic/fixture findings in 91 files and zero findings in its `lake_package` category.

This PR changes none of those owners or root controls. Root-build, pre-push,
and whole-repository release acceptance are not claimed. The PR remains a
draft with focused acceptance documented.

## Mathematical and reproducibility boundaries

The theorem contract in
[TWISTOR_HOMOTOPE_INVARIANTS_CONTRACT.md](../../docs/TWISTOR_HOMOTOPE_INVARIANTS_CONTRACT.md)
states the exact carriers, order conventions, normalizations, and proof
dependencies. The Gram half-trace is a finite Hermitian matrix invariant;
its physical spin interpretation is not constructed. The integer recurrence
does not identify Clifford-space dimensions. Physical group classifications,
quantization, decay limits, and unlimited Grassmannian towers remain outside
the proved scope.

Use the unchanged pinned toolchain and the root-pinned `jsonschema==4.23.0`
dependency. From the repository root:

```bash
python3 verification/twistor-homotope/check.py exe cache get
python3 verification/twistor-homotope/check.py env python3 "$PWD/verification/twistor-homotope/verify.py"
```

The maintained wrapper owns the shared build lock; the driver runs its
subordinate commands sequentially. A report-only follow-up preserves this
receipt and results without changing any protected proof or verification
input from the accepted frozen source.
