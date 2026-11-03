# CAS refactor test infrastructure

[tools/e2e_cas_o1_suite.sh](tools/e2e_cas_o1_suite.sh) is a Bash runner combining
Lean compilation, Python/SymPy diagnostics, static source checks, and elapsed
time measurements. Its historical “CAS O(1) Optimization” name is a campaign
label. The runner does not prove asymptotic constant-time kernel checking.

Source reviewed on 2026-11-03 at commit
`214f7bcf733eaf4720913bc2c082936f2480d3fc`, including the runner, CAS script,
targeted source surfaces, and lock wrappers. This is an implementation guide,
not a fresh passing-run report. Start with [TEST_READY.md](TEST_READY.md) for
readiness and [AGENTS.md](AGENTS.md) for repository operating rules.

## Owners and evidence

| Source | Role in this suite |
|---|---|
| [lean/DAG/DiracLaplacian.lean](lean/DAG/DiracLaplacian.lean) | Lean graph-Dirac declarations and the selected theorem statements scanned by tier 2. |
| [lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean](lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean) | A bridge to projector theorems owned by `Fock` and the CAR witness owned by `RealMajorana`. The bridge uses Lean proof terms; comments referring to CAS scripts are not a runtime import of their output. |
| [lean/DAG.lean](lean/DAG.lean) | Aggregate source whose active Dirac import and elaboration are checked. |
| [scripts/cas_dirac_laplacian_certificate.py](scripts/cas_dirac_laplacian_certificate.py) | Exact rational SymPy matrix diagnostics on a chain, triangle, and digon. |
| [tools/infra/run_locked_lake_build.py](tools/infra/run_locked_lake_build.py) | Shared-lock build wrapper used by tier 1. |
| [tools/infra/run_locked_lean.py](tools/infra/run_locked_lean.py) | Existing shared-lock wrapper for individual Lean source elaboration; the suite's tier 3/4 direct calls do not currently use it. |

The toolchain is pinned by [lean-toolchain](lean-toolchain), and package/build
configuration is in [lakefile.lean](lakefile.lean). Follow those files and the
[root build guide](README.md) rather than a version copied into this guide.

## Tier 1: owner builds and source presence

The runner executes these commands sequentially:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock DAG.DiracLaplacian
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Quantum.NoncommutativeFockBridge
```

It logs a pass for each zero exit status. It also checks that the two source
files exist and each has at least ten lines. The latter check does not parse
namespaces or assess substantive mathematical coverage. The runner does not
independently reject compiler warnings or inspect generated `.olean` files.
The wrapper's workspace-integrity checks reject linked worktrees or symlinked
Lake roots. It attempts cache hydration when needed, without requiring that
subprocess to succeed. Unavailable dependencies can prevent the subsequent
Lake command from succeeding; this wrapper does not perform the separate
package-checkout validation described in the setup guide.

## Tier 2: selected text checks and standard CAS execution

| Check | Implementation | Interpretation |
|---|---|---|
| 2.1 | `grep` for `native_decide` in the Dirac owner. | A literal source-pattern policy for that file. |
| 2.2 | `grep` for `simpa using` in the Fock bridge. | A literal source-pattern policy, not a general classification of that tactic as brute-force search. |
| 2.3 | Regex for `sorry` or `admit` in the two existing target files. | A local text check; it does not inspect imported axioms or establish repository-wide completeness. |
| 2.4 | Runs the CAS script with no arguments and checks the exit code. | Standard fixed-input execution; no invalid-input or boundary-parameter matrix is supplied. |
| 2.5 | Uses `awk` to extract ten named theorem statements, checks required tokens, and applies several negative regexes for known unwanted patterns. | A heuristic source audit. It does not use Lean's AST, compare propositions with git HEAD, or establish arbitrary semantic equivalence. |

The pattern checks can be affected by source layout and comments. Theorem
types, hypotheses, proof dependencies, and targeted builds remain the evidence
for what Lean actually establishes. Passing the token checks cannot rule out
all weakened or unrelated propositions.

## Tier 3: CAS examples and DAG integration

The Python script builds an incidence matrix `B` for each of three fixed
graphs: a three-vertex chain, a three-vertex triangle, and a two-edge digon.
It constructs

\[
D=\begin{pmatrix}0&B^{\mathsf T}\\B&0\end{pmatrix},\qquad
D^2=\begin{pmatrix}B^{\mathsf T}B&0\\0&BB^{\mathsf T}\end{pmatrix}.
\]

The script asserts exact block agreement, zero off-diagonal blocks, and the
trace identity for those examples. The Bash runner checks its exit code and
output keywords. This is an external finite-example diagnostic; the Lean
proofs must establish their own propositions.

The runner then searches for an active `import DAG.DiracLaplacian` in
`lean/DAG.lean` and directly executes:

```bash
lake env lean lean/DAG.lean
```

That is the current implementation, not a locked Lake build of `DAG`. It does
not acquire the repository build lock. A serialized manual source check is:

```bash
python3 tools/infra/run_locked_lean.py --wait-for-build-lock lean/DAG.lean
```

This replacement command does not repair the suite itself or build missing
imports; use the locked Lake wrapper when dependencies need building.

## Tier 4: fixed-file elapsed-time gate

The runner measures each of the same two target source files using
`date +%s` around `timeout 35s lake env lean FILE`.

| Condition | Current result |
|---|---|
| Exit code 124 | Failure: the 35-second timeout expired. |
| Another nonzero exit code | Failure: the command did not complete successfully. |
| Exit zero and measured elapsed time at most 15 seconds | Pass. |
| Exit zero and measured elapsed time over 15 seconds | Failure, even if the 35-second timeout was not reached. |

The measured command includes Lake/Lean startup and environment loading. It is
not an isolated measurement of kernel reduction. A timeout establishes a missed
deadline; the runner's “CPU hang detected” wording does not diagnose the cause.

Neither timed invocation acquires the shared build lock. Check 4.3 only tests
whether `/tmp/info-geometry-build.lock` exists and logs a pass in either case.
It does not inspect a held lock, prove release, or search for orphaned compiler
processes. Tiers 3/4 therefore need a runner change before they meet the
repository's shared-workspace serialization rule. Do not wrap the whole suite
in an outer lock: tier 1 takes that lock internally.

These two fixed-case timings can detect some performance regressions under a
specified environment. They cannot prove an O(1) bound as input or proof size
grows. `rfl` and `exact` describe proof construction steps; their presence alone
does not establish the cost of elaboration or kernel checking.

## Invocation and result contract

The accepted interface is:

```bash
bash tools/e2e_cas_o1_suite.sh --tier 1
bash tools/e2e_cas_o1_suite.sh --tier 2
bash tools/e2e_cas_o1_suite.sh --tier 3
bash tools/e2e_cas_o1_suite.sh --tier 4
bash tools/e2e_cas_o1_suite.sh --tier all --verbose
```

Apply the locking limitation above to tier 3, tier 4, and `all`; these examples
document the interface rather than asserting operational readiness of those
paths. Python/SymPy and the prepared pinned Lean dependencies are prerequisites.

A normal successful `all` run logs 15 successes. Individual failing branches
can log multiple failures, so the total is an implementation counter. Exit zero
means no failures were logged among the selected checks; exit one reports a
failed check or rejected CLI selection. Save the command, commit, dirty-tree
state, versions, log, exit code, and timing environment with every result.
Warnings, semantic fidelity, axioms, and unselected owners require their own
review.
