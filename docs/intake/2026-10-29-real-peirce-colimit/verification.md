# Verification of the real Peirce matrix colimit

**Accepted:** the exact 32-module repository source closure compiles, its
1,104 declarations pass the native axiom/safety audit, and its isolated native
Lake package builds. The seven changed Lean owners compile with warnings
treated as errors and produce no warnings.

The independently accepted code is published at
[`4468137c6b9bfac71874188c816d3fb95b44867b`](https://github.com/nickgou-nuke/info-geometry-lean/commit/4468137c6b9bfac71874188c816d3fb95b44867b).
Subsequent evidence publication adds documentation only.

## Results

| Check | Observed result |
|---|---|
| New mathematical API | 71 public theorems and 6 definitions in 5 new modules |
| Repository import closure | 32 modules compiled |
| Strict targets | 7 owners; 0 compiler warnings |
| Native declaration audit | 1,104 unique declarations, including private/generated auxiliaries |
| Observed axioms | Exactly `propext`, `Classical.choice`, and `Quot.sound` |
| Unsafe/partial declarations | 0 |
| Native isolated Lake build | Passed; 3,180 jobs |
| Staged proof-proxy gate | Passed, exit 0 |
| Constructivity scan | 32 source files; 0 findings |
| Scoped lexical vacuity gate | 7 files; 0 errors; 5 reviewed warning-only proof shapes |
| Source reconciliation | All 32 live, staged, and copied sources match |
| Independent semantic review | Passed; all 12 reviewed path hashes match |
| Dependency reconciliation | Pins unchanged; Mathlib and its 8 transitive packages clean |

The five new modules account for 106 native declarations after generated
auxiliaries are included. The 1,104 total covers the entire repository import
closure, rather than only the newly written theorems.

## Evidence records

- [verification.json](verification.json) is the unmodified final maintained
  verifier output.
- [qa-acceptance.json](qa-acceptance.json) is the unmodified independent runtime
  acceptance record, including declaration counts, source hashes, pins,
  warning details, and evidence-file hashes.
- [semantic-review.json](semantic-review.json) is the independent mathematical
  and source review.
- [source-gates.json](source-gates.json) preserves the final source-gate commands
  and results.
- [github-verification.json](github-verification.json) binds the published code
  blobs to the accepted staged files and records the successful scoped CI run.
- [ci-comparison.md](ci-comparison.md) and [ci-comparison.json](ci-comparison.json)
  compare all seven broader failing workflows with their prior logs.
  [ci-context.md](ci-context.md) preserves the earlier observations.

The SHA-256 of `verification.json` is
`67fec00d04f943d39630dec74e126ae4549d3a33208a74a30e3c088a399e6154`.
The independent acceptance record has SHA-256
`a2fe0f3a5fb98c96a1911f6a3b65a4cc12d8de052745b9cb4d0ff134386edd31`.

The local repository HEAD at validation remained the intake base
`dc3ebf12fdd9ef4e88eb37acffb919e81932061a`; the changes were staged.
The records deliberately retain that fact. Their per-source SHA-256 and Git
blob maps identify the accepted source bytes. All 13 files in the published
code comparison were independently matched against the staged blobs.
The final evidence promotion preserves every accepted source, selector,
workflow, README, and contract hash.

## Scoped GitHub CI

[Run 40901170029](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901170029)
and its
[kernel-check job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901170029/job/123543535499)
succeeded for source head `4468137c6b9bfac71874188c816d3fb95b44867b`.
Its native log reports `PASSED 32 modules; 1104 audited declarations`.

The workflow tested merge revision
`950f8afbda490e76d9756ac40efba40aaf6a1d80`. Comparing that revision with
the source head shows only the two additional Markdown files already on
the base branch; no mathematical source differs.

The retained
[verification artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40901170029/artifacts/12908908892)
contains logs, status records, and the compiled source snapshot. Its archive
digest is
`sha256:6e09b6dbfff12416cc9e4fc2cfdb1e4cf4f6653875d2ee70a44246bd164b0d12`.
The same maintained verifier runs locally and in this workflow.

## Warnings and compatibility

Six compiler warnings remain in unchanged imported owners: one in
`MatrixNoncommutativity`, one in `Decomposition`, one in `SplitQ11`,
and three in `Cl11Matrix`. They concern a deprecated import and
simplification/style suggestions. All seven changed owners have zero warnings.

The separate heuristic source scanner flags five short proofs:
`map_neg_ad_sq`, `ofStage_component10`, `ofStage_component01`,
`ofStageStarAlgHom_apply`, and `lift_of`. Independent review confirms
that they prove native homomorphism identities or definitional evaluation
laws. Their exact warning explanations are retained in the acceptance record;
no gate exception or audit exemption was introduced.

The existing tensor index retains its original recursive equations with a
`noncomputable` modifier. This removes its unnecessary generated executable
unsafe helper while preserving its kernel definition and equation behavior.
The exhaustive rebuilt audit confirms that helper is absent.

The redundant transpose-symmetry argument was removed from
`TowerMatrix.cartan_inv_of_isUnit` and
`Causal.modularMirror_cartan_comm_of_isUnit`. Both statements now need
only the involution and invertibility hypotheses used in their proofs.
Their public arities change: callers must omit the former symmetry argument.
The sole repository call is updated and strictly compiled. Separate Cartan
involutivity theorems retain their required symmetry assumptions.

## Reproduction and scope

Use Lean 4.34.1, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`, as pinned by the repository.

```sh
python3 tools/quality/check_real_peirce_colimit.py \
  --mathlib-root /absolute/path/to/pinned-mathlib \
  --output /absolute/path/to/verification
```

The pinned Lean and Lake executables must be on `PATH`. The maintained
verifier acquires the shared build lock, checks for concurrent compilers,
compiles the exact source closure, audits its native declarations, builds
the isolated Lake package, and reconciles source and dependency hashes.

This acceptance covers that exact closure and isolated package. The seven
broader workflows remain failed for the separately recorded inherited
dependency, configuration, filename-collision, and nonpackage-debt causes.
No repository-root build or all-green repository CI is claimed.

The [contract](contract.md) and [mathematical map](README.md) state the proved
algebraic result and its proof-prerequisite partial order. The full operator
coefficients and actual real matrix quotient are preserved. An analytic
completion, scalar spectral gap, or physical field theory is outside the
proved statements.
