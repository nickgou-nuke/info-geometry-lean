---
name: mission-loop
description: >
  Persistent repo-native mission controller for info-geometry-lean closure debt.
  Two-layer design: Mission layer (persistent state, resume/pause) +
  Heartbeat layer (one constructive replacement per turn, narrow build gate,
  explicit open-problem stop). Wires together closure-debt-constructive-proof-sop,
  lean-proof, and pauli-auditor into a controlled recurrence loop.
version: 1.0.0
author: info-geometry-lean
license: MIT
metadata:
  hermes:
    tags: [lean4, closure-debt, mission-loop, constructive-proofs, mathlib, heartbeat]
    related_skills:
      - closure-debt-constructive-proof-sop
      - lean-proof
      - pauli-auditor
      - lean4
      - closure-mission-loop
---

# Mission Loop

## Two-Layer Architecture

```
┌─────────────────────────────────────────────────┐
│  MISSION LAYER  (persistent across turns)        │
│  goal · subgoal · last_verified · blocker        │
│  .codex/mission/state.json                       │
│  .codex/mission/history.jsonl                    │
└───────────────────┬─────────────────────────────┘
                    │ one socket per turn
┌───────────────────▼─────────────────────────────┐
│  HEARTBEAT LAYER  (one proof per turn)           │
│  classify socket → construct proof →             │
│  lake env lean → lake build → verify/block       │
└─────────────────────────────────────────────────┘
```

The Mission layer remembers where you are.  
The Heartbeat layer does exactly one unit of work and stops.

---

## Command Interface

```
/mission start <goal>              — set standing goal; initialise state
/mission status                    — print full state (goal, subgoal, last verified, blocker)
/mission subgoal <one-step target> — pin next socket (only one active at a time)
/mission next                      — execute one Heartbeat turn on current subgoal
/mission pause                     — freeze loop; state preserved
/mission resume                    — re-activate without resetting state
/mission clear                     — discard all mission state
```

### State Tool

All commands update `.codex/mission/state.json` via:

```bash
python3 tools/quality/mission_state.py <subcommand> [args]
```

Subcommands: `get`, `set-goal`, `set-subgoal`, `verify`, `block`, `classify`, `pause`, `resume`, `clear`, `tick`, `status`

---

## State Schema

```json
{
  "goal":                "native AFP port of JNF corridor",
  "subgoal":             "close basis transport lemma",
  "last_verified":       "SchurDecomposition.basis_repr_smul_head",
  "next_blocker":        "recursive Schur step construction",
  "build_target":        "lake build InfoGeometry.OperatorAlgebra.SchurDecomposition",
  "status":              "active",
  "turns_used":          7,
  "max_turns":           30,
  "consecutive_blocked": 0,
  "scope_file":          "lean/InfoGeometry/OperatorAlgebra/SchurDecomposition.lean",
  "baseline_debt":       4,
  "socket_classification": "closed_by_mathlib"
}
```

Persistent state lives in:
- `.codex/mission/state.json` — current state
- `.codex/mission/history.jsonl` — append-only event log
- `reports/closure/socket-owner-ledger.json` — authoritative socket-to-owner map
- `reports/closure/open-math-problems.md` — registry of hard-stop sockets
- `reports/closure/close-now-lean-tasks.md` — P0/P1 priority queue

---

## Socket Classification

Before attempting a proof, classify the current socket. This is mandatory.

| Class | Meaning | Action |
|-------|---------|--------|
| `closed_by_kernel` | Lean kernel already proves it | Remove debt label, mark done |
| `closed_by_mathlib` | A Mathlib theorem closes it directly | Import + apply + verify |
| `closed_by_repo_owner` | An existing repo theorem closes it | Wire + verify |
| `literature_owned_unformalized` | Known theorem, not in Mathlib | Draft + prove from first principles |
| `open_problem_socket` | Genuinely unsolved math | **HARD STOP** — emit report, do not attempt proof |
| `invalid_or_overclaimed_socket` | The claim is false or malformed | Remove or correct the statement |

```bash
python3 tools/quality/mission_state.py classify <class>
# Exit 1 on open_problem_socket — this is the hard-stop signal
```

**Never advance past an `open_problem_socket` by weakening the statement.**

---

## Heartbeat Layer — One Proof Per Turn

### Step 1: Read authoritative sources

```bash
# Before touching any Lean:
cat docs/CONSTRUCTIVE_CLOSURE_MANDATE.md
cat reports/closure/socket-owner-ledger.json | python3 -m json.tool
cat reports/closure/close-now-lean-tasks.md
```

### Step 2: Select the next socket

Priority order (from `reports/closure/close-now-lean-tasks.md`):
1. P0 — `sorry` holes with a known Mathlib proof
2. P1 — existence-packaging without constructive chain
3. P2 — advisory/soft debt

```bash
python3 tools/quality/mission_state.py status  # check current subgoal
```

If a subgoal was pinned with `/mission subgoal`, use it.  
Otherwise pick the highest-priority P0 item from the task list.

### Step 3: Classify the socket

```bash
python3 tools/quality/mission_state.py classify closed_by_mathlib
```

Exit immediately if `open_problem_socket`.

### Step 4: Prove it (Heartbeat engine)

Follow the `lean-proof` skill exactly:
- One tactic at a time, check diagnostics after each.
- Build the derivation chain comment block:

```lean
-- derivation: <target theorem>
--   ← <supporting lemma 1> (same module)
--   ← <supporting lemma 2>
--   ← Mathlib.<RootConstant>
```

No `sorry`. No opaque witness constructors. No `Classical.choice` as terminal step.

### Step 5: Narrow build gate (two-phase)

```bash
# Phase 1 — file check
lake env lean <scope_file>

# Phase 2 — module build (only if phase 1 passes)
lake build <build_target>
```

Do NOT run a full `lake build` across the whole project. Only the target module.

### Step 6: Update state and report

```bash
# On success:
python3 tools/quality/mission_state.py verify "<TheoremName>"
python3 tools/quality/mission_state.py tick

# On failure:
python3 tools/quality/mission_state.py block "<specific reason>"
```

Emit exactly one line: `Socket <name> closed` or `Blocked: <reason>`.

### Step 7: Choose next socket or stop

```bash
python3 tools/quality/mission_state.py status
```

- If status is still `active` and subgoal is cleared: pick next P0 item → repeat.
- If status is `paused` (budget or 3× blocked): stop, report state.
- If all `close-now-lean-tasks.md` items are done: mission complete.

---

## Loop Exit Conditions

| Condition | State transition | Action |
|-----------|-----------------|--------|
| All sockets in scope verified | `active → done` | Emit completion report |
| Turn budget exhausted (30 turns) | `active → paused` | Stop; `/mission resume` to continue |
| 3× consecutive blocked on same socket | `active → paused` | Stop; escalate or skip |
| `open_problem_socket` classified | loop hard-stops | Write entry to `open-math-problems.md` |
| User sends `/mission pause` | `active → paused` | Freeze state immediately |

---

## Continuation Prompt Template

Used at the start of each `/mission next` turn:

```
[Mission Loop — Heartbeat turn {turn}/{max_turns}]
Goal    : {goal}
Subgoal : {subgoal}
Scope   : {scope_file}
Build   : {build_target}

Last verified  : {last_verified}
Last blocker   : {next_blocker}
Consecutive blk: {consecutive_blocked}

Protocol:
  1. Read docs/CONSTRUCTIVE_CLOSURE_MANDATE.md and reports/closure/close-now-lean-tasks.md.
  2. Classify the socket (mission_state.py classify <class>).
  3. If open_problem_socket: STOP, emit report entry, do not attempt proof.
  4. Prove exactly one socket: one tactic at a time, derivation chain documented.
  5. Run lake env lean {scope_file}, then lake build {build_target}.
  6. Call mission_state.py verify or block.
  7. Emit: "Socket <name> closed" or "Blocked: <reason>".
```

---

## Skill Integration Map

| Skill | Role in this loop |
|-------|------------------|
| `closure-debt-constructive-proof-sop` | Authoritative policy; SOP steps 1–6 apply per socket |
| `lean-proof` | Heartbeat engine: tactic-by-tactic proof construction |
| `pauli-auditor` | Post-mission audit: verify no TSI or lyrical overfit was introduced |
| `lean4` | LSP tooling: goal inspection, premise search, `#print axioms` |
| `afp-isabelle-native-port` | Implementation skill when target is in AFP/JNF corridor |
| `closure-mission-loop` | Original mission loop; use `mission-loop` (this skill) going forward |

---

## Anti-Patterns (Hard Rejections)

| Pattern | Why rejected |
|---------|-------------|
| `sorry` in any new definition | Proof hole, not closure |
| Weakening the theorem statement to avoid a hard case | Hiding the blocker |
| `noncomputable def : T := ⟨witness, trivial⟩` without proof fields | Opaque witness |
| Removing a debt label in a comment without a proof | Textual progress only |
| `Classical.choice _` as terminal proof step | Non-constructive; not Mathlib-rooted |
| Claiming `open_problem_socket` is done because "the literature says so" | Literature ≠ kernel |
| Running `lake build` across the whole project to check one module | Too broad; hides errors |

---

## UTMOST MANDATE

Every promoted proposition must be discharged by a native Lean derivation
chain that traces to Mathlib-rooted constants without vacuous packaging.

`(Native Closure Mandated: Closure Debt)` labels must persist in source
until the kernel-verified proof term exists.

**Real progress = replacing certificate/witness fields with theorem-backed
native derivations that survive `lake env lean` and `#print axioms`.**
