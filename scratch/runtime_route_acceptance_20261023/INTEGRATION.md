# Native runtime acceptance proposal — unexecuted

Candidate: `check_runtime_acceptance.py`, intended for parent promotion to
`tools/infra/check_runtime_acceptance.py` after separate review/QA. No live owner,
workflow, dependency, submodule or pin was changed. No tests/builds were run.

## Exact source mapping

Inspected local HEAD: `67052df96f4ac74649c3357e2a8609b8c6dd061c` with pre-existing
working/index changes. Inspected remote-tracking ref:
`upstream/feat/functional-route-certificates` =
`4b278639fa013a88b67a2565cdeb1564cf70418d` (not freshly fetched).
The remote checker is **tools/infra/check_route_certificate_addition.py**,
not tools/check_route_certificate_addition.py. Its workflow is
`.github/workflows/route-certificate.yml`.

The remote runs three unittest files and hard-codes 19 tests; it clones the
manifest mathlib revision, copies a source closure, and compiles that alternate
project. The proposal retains its eight route inputs and adversarial depth
mutation, but uses native BuildLock, ci_bootstrap and native Lake throughout.
Fixture 7 uses the quoted keyword namespace `namespace.end`.

Native `.github/workflows/ci.yml` already runs root all-default targets at its
Baseline build step. That does not execute these seven Python suites or generated
Lean candidates. Source inventory at drafting time:

| Suite (`tests/test_*.py`) | Defined test methods |
|---|---:|
| attention_polytope | 14 |
| certified_caratheodory | 12 |
| functional_route_fibers | 6 |
| route_certificate | 8 |
| route_diagnostics_torch | 5 |
| shape_sinkhorn_detector | 15 |
| causal_bipartite_sinkhorn | 17 |
| Total | 77 |

These are static method counts, **not execution results**. The runner records
actual collected/run counts independently per suite, requires nonzero complete
execution, and rejects skips, expected failures, failures/errors and unexpected
successes. Three Torch suites currently use module-level SkipTest when Torch is
absent; the runner explicitly requires Torch first. Exhaustive maps inside a
method are not misreported as separate unittest cases.

## Execution and evidence

One nonblocking shared BuildLock covers process precheck, bootstrap, all seven
suites, native targeted dependency build, eight generated file checks and one
negative check. Build/Lean subprocesses launched by the runner inherit the lock descriptor. Interrupting the
parent waits for its active child without killing Lean. An uncoordinated build
or test process causes failure. Cooperative locking is still required from all
other agents; process inspection alone cannot prevent an uncooperative race.

The native target command comes from `tools.infra.build.lake_build_command`.
The runner must not call the lock-acquiring wrapper while already holding the
lock. No copied closure, custom LEAN_PATH, dependency downloads, cache clearing,
pin mutation or alternate Lake project is introduced.

Each positive file must compile with no warnings/errors and exactly the named
`local_certificate`, `certified_inverse`, `certified_minimum` axiom footprints,
limited to propext/Classical.choice/Quot.sound (empty footprints allowed).
The forged file modifies depth after successful Python validation. Acceptance
requires a nonzero Lean exit and a source-positioned error inside the
local_certificate proof, not merely the name appearing in a downstream error.

Artifacts include per-suite counts/logs, preflight report, the actual `lake env lean --version` banner, Git HEAD
and dirty status, generated Lean sources/logs, native target build log, and
before/after-stable SHA256 inventories of native Lean sources, seven runtime
owners/tests, pinned files and checker/lock/bootstrap/build helpers. Failed
runs produce a failed status.json; fresh output directories prevent stale
success reuse.

## Minimal workflow insertion

After the existing successful Baseline build in the same `baseline` job, add
the following steps once the script has been promoted. Existing main push/PR
triggers suffice; no second standalone workflow or new path filter is needed.

```yaml
      - name: Native runtime and generated route acceptance
        run: >-
          python3 tools/infra/check_runtime_acceptance.py
          --out .artifacts/runtime-acceptance-${{ github.run_id }}-${{ github.run_attempt }}
      - name: Preserve native runtime acceptance evidence
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: runtime-acceptance-${{ github.run_id }}-${{ github.run_attempt }}
          path: .artifacts/runtime-acceptance-${{ github.run_id }}-${{ github.run_attempt }}/
          if-no-files-found: warn
```

## Dependencies and open provenance

- Linux/POSIX `fcntl`, `ps`, Git; Python 3.10+ syntax; standard-library unittest.
  No pytest, NumPy import, or third-party test reporter is required by these seven
  suites. PyTorch may have its own transitive package requirements.
- PyTorch is mandatory for the three numerical suites. The remote workflow
  specifies `torch==2.10.0` from `https://download.pytorch.org/whl/cpu`.
  This is remote configuration provenance, not evidence that all seven native
  suites pass on that wheel. The current native CI does not provision this
  dependency: parent must select/approve runner provisioning before enabling
  the step. The candidate installs nothing and changes no dependency pins.
- Native pinned Lean/Lake, manifest packages and local path dependencies must
  be available. ci_bootstrap path failures (including the known atlas/GIFT
  provenance blockers) remain fatal and unmodified. The preflight checks direct
  path-package provenance, not every transitive dependency or package hash.
- Existing native root build remains the full-module coverage authority; the
  incremental certificate target build ensures generated imports are current.
  Source hashes do not independently attest every loaded dependency olean.
- Runtime checks do not prove Python correct or identify floating-point behavior
  with Lean theorems. Generated certificates prove the finite local graph/Drazin
  claims and minimum index, not shell-rank correctness or runtime complexity.
- Pending: execution/diagnostic-format validation on the pinned toolchain,
  independent review, seven-suite Torch compatibility and native preflight repair
  by the owning parent. No success/CI-green claim is made by this draft.
