# Candidate diff: make `hive_swarm` report external QMS review as pending

Status: G-A proposal only. No existing file was edited; no tests/builds were
run. This candidate has not been audited by its author.

## Source-grounded behavior being changed

- `tools/infra/hive_swarm.py:7, 38, 52-65` describes/configures an auditor role
  in the same `SwarmConfig` and `SwarmRun` as generator, critic, and
  formalizer.
- `hive_swarm.py:100-121` sends role prompts through one model endpoint/model
  configuration. `hive_swarm.py:247-250, 300-302` invokes the auditor inside
  the same `run_one` process and task attempt as authoring and Lean checking.
- `hive_swarm.py:180-188` records that response under `auditor` and includes
  `audited` in the state taxonomy. `hive_swarm.py:314-326` makes that response a
  condition for fossilization and marks the goal `audited`.
- The CLI accepts `--auditor-override` at `hive_swarm.py:402` and
  `config_from_args` stores it at `hive_swarm.py:436`.
- `tests/test_hive_swarm.py:36-40, 61-77, 80-109, 112-140` encode the current
  auditor prompt/response and the false implication that a passing in-process
  response yields `audited`.
- `docs/CODEX_AGENT_SWARM_PROTOCOL.md:19-28` currently calls the path a
  generator → critic → Lean formalizer → auditor loop. The same document
  correctly requires independent agent instances at lines 113-119 and says
  automated screening/author checks are not independent audit at lines
  176-177. The opening description must agree with those rules.

## Proposed code delta: `tools/infra/hive_swarm.py`

### A. Remove the in-process auditor as an authority role

Remove `AuditorReport`, `SwarmRun.auditor_report`, `parse_auditor_report`, the
`auditor` branch of `role_prompt`, the auditor entry in `call_role_model`,
`SwarmConfig.auditor_override`, `--auditor-override`, and its construction in
`config_from_args`. Keep generator, critic, and formalizer unchanged.

Rename `audit_and_record` to `record_swarm_run` (it writes a run artifact; it
does not perform an independent audit). Its payload should use an explicit
non-acceptance record, for example:

```python
"qms_review": {
    "status": "pending_external_audit",
    "author_process_review": False,
    "a_a_required": True,
    "qa_a_required": True,
},
"state_taxonomy": [
    "retrieved", "generated", "criticized", "lean_checked",
    "proof_fossilized", "qms_review_pending",
],
```

Do not include an `auditor` verdict, `audited` state, or any implication that
this artifact passed QMS review. For a critic rejection or Lean failure, record
the outcome without an auditor field; those runs do not enter the successful
proof-fossil path.

### B. Keep successful Lean proof capture usable, but leave QMS pending

On `verification["status"] == "success"`, call the existing
`hive_bee.fossilize_success(config.bee, attempt)` without consulting any
auditor prompt. `fossilize_success` in `hive_bee.py:1131-1205` performs the
generated-theorem capture and stores the fossil/replay evidence; it also sets
the goal status to `closed`. Preserve this usable proof artifact and closed
proof state, but add metadata after fossilization:

```python
queue_tool.update_goal_status(
    ..., goal_key_value=str(goal["_key"]), status="closed",
    extra_fields={
        "proof_fossil_key": fossil_key,
        "qms_acceptance_status": "pending_external_audit",
        "qms_a_a_required": True,
        "qms_qa_a_required": True,
        "swarm_run_artifact": str(run_artifact),
    },
)
```

Use the actual fossil key returned by `fossilize_success`; if its return shape
does not expose one at the top level, obtain it from the existing `fossil`
member. Do not overwrite `closed` with `audited`: `closed` continues to mean
that the Lean proof fossil was captured; `qms_acceptance_status` records the
separate pending acceptance state.

Return a status that makes both facts explicit, such as
`"proof_fossilized_qms_pending"`, with `fossil`, `verification`, and
`qms_review_status="pending_external_audit"`. The current return status
`"fossilized"` may be retained as a compatibility alias only if the response
also includes the explicit pending-QMS field and no call site treats that
status as QMS acceptance. Prefer the new status to prevent old consumers from
mistaking it for full acceptance.

The run artifact should be written with the fossil key and the pending QMS
state after successful fossilization. This avoids a record saying “audited” or
omitting the final proof fossil. On critic rejection and failed verification,
keep requeue/deadend behavior, but remove auditor calls and auditor-derived
failure strings/fields.

### C. Avoid claiming independence from labels or process metadata

Do not add a separate `worker_id`, role name, or process-local UUID as a proxy
for A-A/QA-A identity. Such values may help operational lineage, but do not
prove distinct auditor-agent instances or independent reasoning. The return
payload and run artifact must say that external A-A and QA-A are pending, and
only their separately recorded dispositions can update QMS acceptance.

## Proposed test delta: `tests/test_hive_swarm.py`

1. Remove `auditor_override` from `sample_swarm_config`; remove tests for
   `parse_auditor_report` because that API is deleted.
2. Replace `test_run_one_success_with_all_roles` with a test where generator,
   critic, and Lean verification succeed. Assert:
   - `fossilize_success` is called once;
   - result is `proof_fossilized_qms_pending` (or the agreed compatibility
     status plus explicit metadata);
   - result and run artifact state `qms_review_status` as pending;
   - the goal is not updated to `audited` and no `auditor_verdict` is written;
   - the proof goal remains `closed` after fossilization, while its QMS
     acceptance field remains pending.
3. Assert `call_role_model` is invoked only with `generator` and `critic` roles
   during a successful `run_one`; no hidden auditor call occurs on critic
   rejection or verification failure.
4. Retain the critic rejection/requeue test, removing `auditor_override` and
   assertions about `auditor` output.
5. Add a failure test showing Lean verification failure never calls
   `fossilize_success` and never records QMS acceptance.
6. If a compatibility status alias is retained, explicitly test that it still
   carries `qms_review_status="pending_external_audit"` and is never named or
   interpreted as `audited`.

These are proposed acceptance assertions, not test results.

## Proposed documentation hunk: `docs/CODEX_AGENT_SWARM_PROTOCOL.md`

Replace the opening Hive description around lines 19-28 with wording such as:

```diff
-  `hive_swarm.py` implements a generator → critic → Lean formalizer → auditor
-  loop, while separate build, audit, and promotion workers record later gates.
+  `hive_swarm.py` runs generator → critic → Lean formalization in one worker
+  process. Its role prompts are not an independent audit. Successful Lean
+  proof capture may be fossilized and reported with QMS acceptance pending.
+  Separate Hive build/audit/promotion workers record operational workflow
+  gates; their configured labels or process UUIDs do not establish QMS
+  independence. QMS acceptance requires a distinct A-A and QA-A agent context,
+  read-only audit evidence, and the required independent checks.
```

Also add a brief status distinction in the workflow section: “proof fossilized”
means the existing Lean capture/fossil path completed; “QMS accepted” means the
separate A-A and QA-A cycle completed. The first can be useful before the
second, but cannot satisfy or imply it.

## Behavior and compatibility impact

- Successful proof capture remains available and is no longer blocked by a
  same-process model response. It reports QMS as pending until external A-A and
  QA-A results are recorded.
- The goal proof state may still be `closed` through the existing fossilizer;
  it must not be marked `audited` by `hive_swarm`.
- The result object stops returning `auditor` and instead returns explicit QMS
  pending metadata. Consumers that require `result["auditor"]` or branch on
  `status == "fossilized"` must be migrated.
- The `--auditor-override` CLI flag and `SwarmConfig.auditor_override` field are
  removed. Existing scripts supplying them must stop doing so. An alternative
  is to accept the old flag temporarily but ignore it with a deprecation error;
  it must never affect proof fossilization or acceptance status.
- Critic and Lean verification behavior remains unchanged. Rejected/failed
  attempts still requeue or deadend; their records no longer contain an
  in-process “auditor” verdict.
- This change does not assert that Hive's operational AuditBee is itself the
  repository's independent QMS A-A. A separate Codex auditor agent and QA-A
  agent remain required by the QMS role-separation SOP.

## Independent audit handoff

This proposal is G-A output. A separate A-A must inspect the exact eventual
source diff for authority/status semantics, compatibility, and regression
coverage. A distinct QA-A must then rerun the relevant tests and verify that no
successful path writes `audited` or accepts QMS based on `hive_swarm`'s own
prompts. No such checks were run for this proposal.
