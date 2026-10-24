# Native reviewed65 independent QA preparation — NOT EXECUTED

Candidate inspected: `scratch/reviewed_native65_20261023/native_reviewed.py`, SHA-256
`653525b27418fe33bdf61f228052edd13bd5689ba3c1b070bc20a470647f591a`.
This is a draft baseline, not the final freeze. No test, candidate import, build,
submodule initialization, cache repair, or native acceptance run was performed.
G-A Kepler; A-A James pending. Parent will announce final code/A-A freeze.

## Planned execution boundary

After freeze, inspect final CLI integration and hash the candidate/promoted owner,
checker, specification, tests and workflow. Queue once on shared BuildLock after
process precheck; pass its descriptor to every spawned QA child. Preserve stdout,
stderr, exit status, source hashes and mock-vs-real classification in a fresh /tmp
artifact directory. Never nest actual acquisition of this same lock in a mocked
run_native test. Do not build the full 56/65 union on this checkout. Current
Atlas/GIFT/Architect provenance blockers must remain explicit.

## Draft fixtures supplied

`test_candidate.py` contains unexecuted, temporary-directory fixtures for clean
mocked provenance, wrong revision, dirty/untracked/staged package, dirty root,
wrong repository root, nested gitlinks, duplicate names, unsupported subDir,
escaping provider, warm build preservation, cached Lake config rejection, wrong
cwd, existing output, and preflight failure report with exact target preservation.
No mock-clean result can become actual provenance or kernel evidence. Fresh
output in these tests is a temporary fake root; nothing touches native owners.

## Final integration tests to add after CLI exists

The current live `check_reviewed_prs.py` has no native branch, so do not invent its
flag names now. Test direct-script and package imports, help/dispatch, default
legacy behavior, native mathlib-argument independence if promised by final CLI,
wrong cwd/output failures, and propagation of nonzero native failure to CLI exit.

Drive run_native using a temporary fake repository and mocked external commands:

1. Supply the exact ordered live specification (65 targets), validate roles and
   retain every target exactly once in the native `lake build` argv. No copied
   import closure or alternate lakefile. Assert `--offline`, `--no-cache`,
   `--rehash` placement against pinned Lake's actual accepted CLI syntax.
2. Mock a stable provenance identity only to reach subsequent control flow. Assert
   all roles are explicitly rerun; success cannot be supplied by cached command
   artifacts. Parse every owner count and role marker from generated audit output.
3. Simulate version, build, command-module, context, audit and probe failures.
   Retain stdout/stderr logs, exact argv, exit status and failed report; no later
   success marker. Exercise Popen spawn failure separately from nonzero exit.
4. Assert each Popen receives the context manager's actual descriptor and a new
   session. Exercise KeyboardInterrupt followed by child completion: no terminate,
   kill or premature unlock; report failed/interrupted. A real tiny Python child
   may fstat the inherited descriptor after final authorization, under shared lock.
5. Reject absolute artifact providers, project paths outside approved build libs,
   symlink escapes, context drift, changed command-only source and final provenance
   drift. Distinguish absent/cold cache from unknown preexisting artifacts; never
   delete either root or dependency caches to manufacture a passing test.
6. Supplement mocked git checks with tiny NEW local Git repositories after freeze:
   exact installed commit accepted; commit mismatch/untracked/staged dirt rejected;
   own-repository identity checked. No network or installed dependency changes.
7. Run read-only real `path_package_report` / source_identity if authorized by the
   freeze, retain actual Atlas/GIFT/Architect rejection and prove no compiler was
   spawned. This is a negative preflight result, not a native reviewed65 success.

## Source questions for A-A/final freeze

- `run_native` checks target count 65; preservation tests must compare the entire
  ordered committed specification, not use count alone as proof of exact identity.
- Candidate acquires the shared lock internally. The QA orchestration must not
  wrap an actual run_native call in a second nonreentrant lock; mock its lock only
  for isolated control-flow tests, not for real acceptance.
- The runner accepts `**kwargs` from the context-manifest helper but does not
  forward them. Inspect actual helper requirements before calling that compatible.
- Cold-root/dependency policy is intentionally stricter than this warm development
  checkout. No deleting caches, overriding provenance, or claiming CI success.
- No final CLI integration test can pass before the integration exists.

Acceptance report will separate (a) Python/mock control-flow tests, (b) actual
small native fixtures, (c) actual provenance rejection, and (d) full native
acceptance NOT RUN/BLOCKED. Existing positive generated-audit evidence remains
independent of this native-runner candidate.
