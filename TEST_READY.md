# CAS refactor test suite: readiness and limits

The runner is [tools/e2e_cas_o1_suite.sh](tools/e2e_cas_o1_suite.sh). It checks
two Lean owners, a small graph-matrix certificate script, selected source
patterns, DAG import wiring, and two elapsed-time thresholds. This page does
not assert that the suite passes on the current checkout.

Source reviewed on 2026-11-03 at commit
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. No new suite execution was performed
for this documentation review. The earlier “15/15 verified passing” statement
is historical and was not tied here to a reproducible run at this commit.

## What is ready to inspect or run

| Tier | Implemented behavior | Material limit |
|---|---|---|
| 1 | Builds `DAG.DiracLaplacian` and `InfoGeometry.Quantum.NoncommutativeFockBridge` with the shared locked wrapper; checks source existence and a minimum line count. | Success is based on exit codes and file checks, not a separate warning-free or namespace audit. The wrapper checks workspace layout and attempts cache hydration; package-checkout validation is a separate step. |
| 2 | Searches for `native_decide`, `simpa using`, `sorry`, and `admit` in the selected files; runs the CAS script on its fixed inputs; checks theorem-statement text and selected patterns. | This is text/regex analysis, not an AST or git-HEAD comparison. It does not prove semantic equivalence or exhaustively test invalid inputs. |
| 3 | Runs the CAS script and checks its output keywords, checks the active DAG import, and invokes `lake env lean lean/DAG.lean`. | The direct Lean invocation does not acquire the shared build lock. |
| 4 | Runs two direct `lake env lean` commands under `timeout 35s`, requiring measured elapsed time of at most 15 seconds; inspects whether the lock file exists. | The commands do not acquire the shared lock. Fixed-case timings do not prove asymptotic O(1) complexity. The lock-file test passes in both branches and does not establish lock ownership or process cleanup. |

See [TEST_INFRA.md](TEST_INFRA.md) for the exact checks and interpretation.
The normal all-pass path logs 15 successes; the counter is not an independent
coverage guarantee and can vary when multiple failures are logged.

## Recommended initial checks

Run from the repository root after following the [build setup](README.md) and
[AGENTS.md](AGENTS.md):

```bash
bash tools/e2e_cas_o1_suite.sh --tier 1
bash tools/e2e_cas_o1_suite.sh --tier 2
```

For a separately serialized check of the DAG aggregate source:

```bash
python3 tools/infra/run_locked_lean.py --wait-for-build-lock lean/DAG.lean
```

The locked source check requires its imported artifacts to be prepared; use
the locked Lake build wrapper for missing owner dependencies. Preserve the
shared `.lake` cache.

## Full-suite interface and outstanding runner work

The existing CLI accepts `--tier 1`, `2`, `3`, `4`, or `all`, plus `--verbose`:

```bash
bash tools/e2e_cas_o1_suite.sh --tier all --verbose
```

Before using tiers 3/4 or `all` as a shared-workspace gate, route their direct
Lean calls through the repository locking mechanism. This documentation update
does not repair those calls. Wrapping the entire suite in an outer lock is not
a substitute: tier 1 acquires the same lock internally. Until the runner is
repaired, report the limitation alongside any historical or separately
scheduled full-suite run.

The historical name “CAS O(1)” describes the refactor campaign. The implemented
performance gate uses a **35-second termination timeout** and a separate
**15-second maximum passing elapsed time**. Timing two fixed source files,
or replacing a proof with `rfl`/`exact`, does not establish a complexity bound
over a growing family of inputs.

## Evidence to attach to a result

Record the commit and working-tree changes, exact command and selected tier,
toolchain and dependency state, exit code, output log, and any measured times.
State whether locking was provided. An exit code of zero means the checks
actually executed by that invocation logged no failure; it is not a global
proof-completeness, semantic-equivalence, or all-backend certificate.
