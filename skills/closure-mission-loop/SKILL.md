---
name: closure-mission-loop
description: >
  Eternal mission loop for native Lean closure debt in info-geometry-lean.
  Wraps the standing-goal state machine with a heartbeat runner that selects
  one open socket per tick, runs Lean/judge/gate checks, and immediately
  re-arms on the next debt.
version: 2.0.0
author: info-geometry-lean / Hermes
license: MIT
metadata:
  hermes:
    tags: [lean4, closure-debt, mission-loop, heartbeat, constructive-proofs, mathlib]
    related_skills:
      - closure-debt-constructive-proof-sop
      - hive-goal-loop
      - formalizer_loop
      - lean4
      - pauli-auditor
---

# Closure Mission Loop

## Purpose

This skill defines the repo-native **eternal mission loop** for paying
`(Native Closure Mandated: Closure Debt)` one socket at a time.

The mission never becomes globally "done". Only individual sockets close.
After a socket is closed, the mission re-arms on the next open debt and keeps
running until the user pauses or clears it.

The implementation boundary is:

- `tools/infra/goal_loop.py` owns standing-goal persistence and continuation
  prompts.
- `tools/infra/mission_loop.py` owns mission state, socket selection, and
  heartbeat packets.
- `tools/quality/mission_judge.py` decides socket closure for one proof turn.
- `tools/quality/check_closure_debt_gate.py` blocks regressions on the selected
  closure frontier.
- `tools/infra/hive_qi_heartbeat.py` can ingest heartbeat log output later.

---

## Command Interface

Use the actual repo script:

```bash
python3 tools/infra/mission_loop.py set "Pay the Native Closure Debts of the repository"
python3 tools/infra/mission_loop.py status
python3 tools/infra/mission_loop.py heartbeat --run-build --run-gate --lean-file <file> --response-file <file> --baseline-debt <n>
python3 tools/infra/mission_loop.py pause
python3 tools/infra/mission_loop.py resume
python3 tools/infra/mission_loop.py clear
```

Recommended defaults:

- mission text: `Pay the Native Closure Debts of the repository`
- ledger: `reports/closure/socket-owner-ledger.json`
- goal state: `artifacts/goal-loop/`
- mission state: `artifacts/mission-loop/`
- heartbeat log: `artifacts/hermes_loop/heartbeat/native_closure_mission.log`

---

## Loop Mechanics

### 1. Mission Start

`mission_loop.py set` initializes a persistent mission record and also seeds the
standing goal state in `goal_loop.py`.

The standing goal is the mission text itself. The selected socket is tracked as
a subgoal / current target.

### 2. Socket Selection

Each heartbeat tick selects the next open socket from the structured closure
ledger.

Default source:

```bash
reports/closure/socket-owner-ledger.json
```

Selection rule:

- skip sockets already marked closed in the mission record
- skip sockets whose status is terminal
- choose the first remaining open socket in ledger order

### 3. Heartbeat Tick

Each heartbeat tick is finite and must not be expanded with brute-force
controls.

Minimum tick contract:

1. Load mission state.
2. Select or retain the current open socket.
3. Sync the standing goal and current subgoal.
4. Optionally run the target Lean build.
5. Optionally run the closure-debt gate.
6. Optionally run `mission_judge.py` with a Lean file, response file, and
   baseline debt count.
7. Append a persistent heartbeat packet.
8. If the socket closes, re-arm on the next open debt.

### 4. Judge Gate

The judge for a socket is deterministic and repo-local:

- `lake env lean <file>`
- no new forbidden witness patterns
- debt count reduction versus baseline
- derivation chain documented in the response

The judge verdict is socket-level only. The top-level mission remains eternal.

### 5. Continuation Prompt

The continuation prompt comes from the standing goal state in
`tools/infra/goal_loop.py`. It should always name the mission and preserve the
current socket target.

### 6. Exit / Pause Conditions

| Condition | Status |
|-----------|--------|
| User pauses the mission | mission paused |
| User clears the mission | mission cleared |
| Lean toolchain error unrelated to the socket | tick blocked and mission paused |
| Socket closes successfully | socket closed, mission re-arms on next open debt |

The mission itself is not marked done by socket closure.

---

## State Persistence

Mission state:

- `artifacts/mission-loop/<session>.json`

Standing goal state:

- `artifacts/goal-loop/<session>.json`

Heartbeat log:

- `artifacts/hermes_loop/heartbeat/native_closure_mission.log`

The mission state records the current socket, closed sockets, tick count, and
notes. The standing goal state records the continuation prompt and subgoals.

---

## Integration with Existing Skills

| Skill | Role |
|-------|------|
| `closure-debt-constructive-proof-sop` | Native proof closure policy; no witness packaging as final closure |
| `hive-goal-loop` | Outer recurrence semantics and user preemption discipline |
| `formalizer_loop` | Local theorem repair and premise tightening inside one proof turn |
| `lean4` | Lean kernel inspection and proof debugging |
| `pauli-auditor` | Post-promotion audit for promoted theorems |

This skill wraps those loops. It does not replace them.

---

## Anti-Patterns

- Do not make the mission terminal at the repository level.
- Do not use `maxHeartbeats` or any equivalent force knob to fake progress.
- Do not promote witness scaffolding as complete closure.
- Do not hop modules after a build failure unless the current module is structurally blocked.
- Do not collapse the mission into one theorem; one socket per tick.
- Do not let textual progress stand in for a kernel-checked change.

---

## UTMOST MANDATE

Replacing witness-gated and external-certificate leftovers with native Lean
proofs is the top priority.

- Witness packets, certificate fields, external certificates, and assumption
  interfaces are temporary scaffolding only.
- Every promoted proposition must be discharged by native Lean derivation or an
  imported mathlib theorem.
- Socket debt stays open until the kernel-checked proof term exists.
- Progress is structural, not rhetorical.
