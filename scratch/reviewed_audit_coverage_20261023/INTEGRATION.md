# Reviewed audit coverage — revised parent-approved role contract

Sandbox proposal only; no tests, builds, or Lean elaboration performed. Preserve
all 65 selected targets, including both command-only modules and all nine added
owners. This is not Architect dependency support or a claim of CI acceptance.
No existing owner/workflow/manifest/pin is changed.

## Exact source-backed roles

`reviewed_audit_source.py` freezes an immutable exact mapping and SHA256 of the
inspected command sources. No suffix, namespace, or empty-source heuristic.

- `InfoGeometry.Algebra.CuntzClifford22Audit` imports
  `InfoGeometry.Algebra.CuntzClockObstructions`, which imports
  `InfoGeometry.Algebra.CuntzClifford22`. Its eight `#print axioms` commands refer
  to these two selected declaration owners.
- `InfoGeometry.Krein.TransitionWeakValueAudit` imports
  `InfoGeometry.Krein.TransitionWeakValueExamples`, which imports
  `InfoGeometry.Krein.TransitionWeakValue` and
  `InfoGeometry.Canonical.WeakValuePoleBounds`. Its twelve `#print axioms`
  commands refer to these three selected declaration owners (including the
  current `sampled_gradient_energy_lower_bound` command).

Both role sources contain imports/comments/commands, no authored declarations.
Runtime confirmation is required: the combined environment must contain each
selected module in `env.header.moduleNames`. Exactly these two must own ZERO
actual environment declarations; every other selected module must own at least
one. Ownership is `getModuleIdxFor?`, not namespace matching. The combined scan
still examines ALL selected declarations, including any accidentally added to
command modules, before rejecting that role mismatch. Each declaration uses PUBLIC `Lean.collectAxioms name`; returned arrays are
checked individually and unioned without duplicates into a sorted axiom summary.
Unsafe/partial rejection and the exact three-standard-axiom allowlist remain.
No private collector call or caller-managed collector state remains. Positive global count alone never establishes coverage.

The optional explicit `command_only` argument is a list/tuple of module names.
Unknown, nonselected, duplicate, incomplete or malformed entries fail. Every
mapped dependency owner must remain selected and have positive coverage; it
cannot be assigned a command-only role. The immutable allowlist is not a
user-configurable escape hatch. Changing roles/source hashes requires source
review; the owner checks must never be removed to make a role change pass.
Target validation remains nonempty/unique, ASCII dotted Lean identifiers with
quoted components, including keyword components such as `namespace.end`.

## Minimal live integration instructions (not applied)

Promote the helper to `tools/quality/reviewed_audit_source.py`. Replace the live
`audit_source` definition by imports of `audit_source`, `validate_targets`,
`validate_roles`, `check_command_sources`, `may_reuse_cache`. Use a relative
import for package invocation and direct helper import for script invocation.
Promote fixtures to `tests/test_reviewed_audit_source.py`, updating their import.
Include helper/tests in workflow path filters and checkout scope.

At intake, BEFORE output creation, dependency traversal or interpolation:

```python
targets = validate_targets(specification['targets'])
roles = validate_roles(targets)  # exact immutable mapping, no target omission
check_command_sources(repo / 'lean', targets, roles)
```

Keep the complete target list, existing closure, combined audit, and proof probe.
After copying closure sources, call `check_command_sources(source, targets, roles)`.
Use a fresh per-run output directory; never reuse a previous success report.

In the existing ordered compilation loop, change only cache eligibility:

```python
if may_reuse_cache(module, targets, roles) and metadata and metadata.is_file():
    # existing cache verification/copy/continue body, unchanged
```

Thus even an exact cache hit cannot skip a selected command-only module.
The existing synchronous `subprocess.run(['lean', '-o', destination, sourcefile],
...)` elaborates its copied .lean source afresh under the SAME build lock and
existing process precheck. Calling Lean directly on the source does not use the
module's olean as a substitute for elaborating that source. Its imported owners
may use validated artifacts; merely importing the Audit olean in the combined
run is NOT fresh command execution. Do not add a parallel compiler, cache
cleaning, or source stub. The command module may still produce/cache an olean
for downstream imports, but its cache entry must never suppress this run.

Retain the existing per-module stdout/stderr log on success AND failure. Extend
each fresh compilation report entry with `cached: False`, `exit_code:
result.returncode`, `log: module + '.log'`, and `role: 'command-only'` for mapped
modules (otherwise `'owner-or-dependency'`). A blocked dependency must remain
blocked, never passed. Before final success require exactly one report entry
for each mapped module, status passed, cached false, exit_code 0, and a retained
log. Do not infer success from log contents or an early marker.

Generate `audit_source(targets, roles)`. For the combined audit, replace the
current raising `run` wrapper with synchronous capture/write-log/record-exit
BEFORE checking returncode, so failures also retain `axioms.log`. Require zero
terminal exit and the existing unique positive `AUDIT_COUNT`, plus exact role
marker sets (`AUDIT_MODULE` for owners, `AUDIT_COMMAND_MODULE` for the two roles).
Also parse `AUDIT_MODULE_COUNT: <module>: <natural>`: require exactly one
count for every selected target, no unknown/duplicate count entries, zero for
both command roles, positive for every owner, and sum equal to `AUDIT_COUNT`.
Retain numeric counts in the report. Partial count output on a failing run is
not acceptance. The role marker only certifies presence/zero ownership: fresh command execution is
established separately by the compilation records, never by this marker.

Immediately before success recheck command hashes in BOTH live and copied trees.
Bind the helper SHA256, role mapping, and command-source hashes into the run
report/audit provenance. Preserve and compare closure-wide initial/final source
fingerprints (including copied bytes) as required by the native support design;
source drift invalidates acceptance. Do not replace native dependency provenance
with these two hashes. Use the current helper hash in audit-result cache identity;
never reuse a prior combined-audit result. Full native Architect support remains
separate, requiring clean exact-pin compatibility, not dirty local oleans.

## Deferred acceptance checks

The 23 Python unittest fixtures check validation, generated text, immutable
mapping, source-drift rejection, cache eligibility, and retention of safety scan
structure. They do NOT run Lean, a subprocess/cache integration, or prove that
module presence/ownership APIs behave as intended. No fixtures were run here.

After shared lane availability, run Python fixtures serially with process
precheck/shared lock. Separately require pinned-Lean integration fixtures:

1. Positive owner coverage, missing owner coverage, ownership in a different
   namespace, private/generated declarations, unsafe/partial and extra-axiom
   rejection; quoted `namespace.end` import/Name syntax.
2. Real two command modules present, zero-owned, all five selected owners audited.
   Emptying/changing a command source fails its reviewed hash. Adding a declaration
   must fail zero-owned coverage even if a future source review updates its hash.
3. Prepopulated valid command-module cache still launches fresh source elaboration
   on EVERY invocation; test two successive runs. Retain command output and zero
   terminal exit both times. A deliberately failing command must leave its log
   and nonzero exit, fail the run, and never gain acceptance via cached olean.
4. Missing/nonselected/duplicate role, removal of any required selected owner,
   missing imported-module presence, blocked dependency, interrupted subprocess,
   missing completion/report/log, and source drift each fail closed.

These integration tests are requirements, not results. No target reduction,
import stripping, dependency-source edits, pin updates, or dirty-cache trust.

## James reviewer handoff

Revised scope: exact two command-only roles, zero-owned + imported presence,
positive owner coverage for all remaining targets, five mandatory selected
owners, fresh source elaboration despite cache hits, retained logs/exit status,
and immutable source-reviewed mappings. Please review the candidate and deferred
integration contracts; no Lean/Python acceptance result is claimed.

## Public Lean API correction — parent handoff to James

Read actual installed pinned source:
`/home/goutev/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Lean/Util/CollectAxioms.lean`.
It declares `private partial def collect (extFind? : Environment → Name →
Option (Array Name)) (c : Name) : M Unit`, whereas its public entry point is
`public def collectAxioms [Monad m] [MonadEnv m] (constName : Name) : m (Array Name)`.
The public implementation sets the private environment view and consults the
exported axiom extension internally. The sandbox now uses only that public
entry point once per enumerated selected declaration. It intentionally gives up
caller-shared collector state; correctness and API compatibility take precedence.
No private internals are invoked by generated code.

Counts accumulate by actual declaration module ownership after safety checks.
Every selected target receives a numeric count, including exact zero for both
command roles, before role validation and final success. Existing presence,
source-hash, required-owner, cache-bypass and fresh-command contracts remain.
Fixtures now reject private API references, inspect the public call/array union,
and inspect count initialization/increment/emission and zero/positive guards.
These are unexecuted Python source fixtures, not evidence of Lean elaboration.
Please relay this revision to James through the parent; no direct notification
was sent. The reported 171-head attention audit is precedent supplied by the
parent, not a verification result for this candidate.
