# Mission Loop SOP

> Status: `current policy`
> Scope: native Lean closure-debt runs, AFP/JNF ports, long-lived heartbeat sessions.

The mission loop is the repo's persistent control surface for paying native
closure debt. It is not proof authority. It never declares the repository
"done"; it only advances the current debt frontier.

## Invariants

1. The standing mission is eternal until the user pauses or clears it.
2. `docs/ClosureDebtLedger.md` is the authoritative backlog.
3. Every heartbeat selects the smallest payable native target first.
4. Narrow build gates come before broad audits.
5. Open problem sockets are reported, not disguised as closures.
6. Witness/certificate surfaces are only closed by kernel-checked Lean or
   imported mathlib theorems.
7. User messages preempt continuation for that turn.
8. The judge remains strict JSON and fail-open on parse errors.

## Execution Order

1. Read `docs/ClosureDebtLedger.md`.
2. Read the current loop state in `artifacts/goal-loop/`.
3. Pick the next smallest payable target.
4. Patch exactly one theorem surface or one constructor surface.
5. Run the narrowest build first, usually:

```bash
lake build <Touched.Module>
```

6. If the target affects a frontier group, run the relevant gate:

```bash
python3 tools/quality/check_closure_debt_gate.py --policy tools/quality/closure_debt_gate.json
python3 tools/quality/check_frontier_integrity_gate.py --config tools/quality/frontier_gate.json --json-out reports/dag/frontier-gate-report.json
```

7. Use `scripts/quality/strict-check.sh` only as the outer audit spine.
8. Record the verified theorem or the explicit open-problem socket.
9. Immediately select the next payable target.

## CLI

Set a standing mission:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" set \
  "Pay native closure debt forever, one kernel-checked target at a time"
```

Add a subgoal:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" subgoal \
  "Close the smallest payable target and verify it narrowly"
```

Render the next continuation prompt:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" continuation
```

Apply a strict judge verdict:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" judge \
  --json '{"done": false, "reason": "next target remains open"}'
```

Pause, resume, clear, and inspect:

```bash
python3 tools/infra/goal_loop.py --session "$SESSION_ID" pause --reason "user preempted"
python3 tools/infra/goal_loop.py --session "$SESSION_ID" resume
python3 tools/infra/goal_loop.py --session "$SESSION_ID" clear
python3 tools/infra/goal_loop.py --session "$SESSION_ID" status
```

## Mission Rule

The loop is successful only when each turn produces one verified native Lean
closure or one explicit open-problem report. It is not successful because the
goal text is inspiring, because a witness exists, or because a broad build was
green once.
