# OS–epistemic compiler bridge

Status: implemented source; Lean compilation, axiom audit, and Python regression
execution are pending the shared build lock. No live worker was started or
reconfigured for this integration.

## Existing owners, one connection

```text
reviewed finite partial order + declaration/Expr requests
  → FiniteDependencyCompiler.compile
  → HiveBridge.PreparedPlan
  → KernelContractAudit.requireAdmission
  → HiveBridge.emitAdmission
  → hive_epistemic_bridge.check_admission_output
  → hive_workflow_policy.check_workflow_policy
  → existing build/audit/promotion gates (still required)
```

`lean/InfoGeometry/Meta/HiveEpistemicBridge.lean` does not implement another
scheduler. `PreparedPlan` retains the existing compiler's success equation and
the exact association of the computed schedule with its declaration requests.
Its validity and permutation theorems reuse `compile_sound`.

`prepare pending request` captures the current kernel environment. The caller
supplies a finite partial order and independently reviewed propositions; graph
labels are not proof evidence. Before dispatch, `withAdmission` reruns the native
audit of declaration freshness, dependency closure, actual dependency order,
proposition matching, allowed axioms, and QMS admission. It does not accept cached
admission booleans. Duplicate declaration aliases are rejected by that audit.

`emitAdmission plan` uses this same gate to emit one aggregate JSON line prefixed
`[hive-epistemic-admission]`. A caller in a Lean elaboration context can use:

```lean
let plan ← InfoGeometry.MetaCompiler.HiveBridge.prepare pending request
InfoGeometry.MetaCompiler.HiveBridge.emitAdmission plan
```

Here `pending : List Node` and `request : Node → KernelContractAudit.Request`
must already be defined. The regression module instantiates this interface with
the existing two-theorem test chain. Those deliberately thin owner proofs remain
QMS-review cases: dispatch and receipt emission must be blocked, not overridden.

## OS policy interface

The existing Python workflow policy now accepts an explicit opt-in gate:

```python
check_workflow_policy(
    mode="checkpoint",
    before_files=before_files,
    after_files=after_files,
    epistemic_required=True,
    epistemic_execution={
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "module": checked_module,
    },
    epistemic_declarations=reviewed_scheduled_declarations,
)
```

Supply the normal build/axiom gate results separately. The expected declaration
list must come from the reviewed schedule contract, not be copied from the
receipt being checked. Providing either epistemic input enables the gate even
without `epistemic_required=True`. Missing, ambiguous, mismatched, non-admitted,
or failed-process evidence blocks it. Marker-scan overrides do not bypass it.

The existing CLI exposes `--epistemic-required`, `--epistemic-execution-json`,
and repeatable `--epistemic-declaration` arguments. Existing lanes remain unchanged
until explicitly opting in; no daemon configuration or queue state is modified.

The adapter emits the existing `VerificationRecord` format with authority
`policy`, not `kernel`. It never grants promotion. It does not implement a new
packet store, Arango collection, scheduler, or external checker.

## Trust boundary

JSON and log markers are not authenticated proof certificates. This adapter is
for output captured from a trusted Lean process after successful termination,
not arbitrary agent-submitted logs. The trusted runner remains responsible for
the executable, current imports, source/artifact freshness and the reviewed
specification. A process-local kernel snapshot does not establish disk freshness
or authenticity after serialization. The Python parser has no theorem proving
its correspondence to Lean's implementation. Full live-worker deployment and
artifact-bound replay protection remain separate work.

The finite scheduler and admission bridge also do not establish any new
topological, homological or analytic-colimit theorem.

## Sequential validation

Inspect host compiler processes first. Once the shared lock is free:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Meta.HiveEpistemicBridgeTests
```

Review the test module's `#print axioms` output. Then, under the same shared lock
discipline and with no concurrent compilation, run
`pytest tests/test_hive_epistemic_bridge.py tests/test_hive_workflow_policy.py`.
Python receipt fixtures test the parser only; they are not Lean certificates.
