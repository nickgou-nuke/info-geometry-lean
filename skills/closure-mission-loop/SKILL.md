---
name: closure-mission-loop
description: >
  Persistent recurrent loop that drives native-proof closure of Lean debt sockets
  in info-geometry-lean. Modelled on the Hermes /goal loop but with a Lean-kernel
  judge gate instead of a language-model verdict.
version: 1.0.0
author: info-geometry-lean / Hermes
license: MIT
metadata:
  hermes:
    tags: [lean4, closure-debt, mission-loop, constructive-proofs, mathlib]
    related_skills:
      - closure-debt-constructive-proof-sop
      - hive-goal-loop
      - formalizer_loop
      - lean4
      - pauli-auditor
---

# Closure Mission Loop

## Purpose

A **persistent, self-judging work loop** for eliminating `(Native Closure Mandated:
Closure Debt)` sockets one constructive proof at a time.

It adapts the Hermes `/goal` mechanics (set → judge → continue/done) to this
repo's strict closure standard:

- Judge gate is the **Lean kernel** (`lake env lean`), not an LLM.
- DONE requires: kernel pass + zero new witnesses + each closed socket has an
  explicit Mathlib derivation chain.
- State persists in the session SQL `todos` table so `/resume` works across
  compaction boundaries.

---

## Command Interface

```
/mission set "<scope>"         — start a new mission loop on a scope
/mission status                — print current loop state and open socket count
/mission subgoal "<theorem>"   — pin a specific socket as the next target
/mission pause                 — suspend the loop (preserves state)
/mission resume                — re-activate a paused mission
/mission clear                 — discard current mission state
```

`<scope>` is a Lean module path or file glob:

```
/mission set "lean/InfoGeometry/Geometry/SpectralDivisors.lean"
/mission set "lean/InfoGeometry/Canonical/*.lean"
```

---

## Loop Mechanics

### 1 — Discovery Pass (once per mission)

Before the first continuation turn, run the deterministic scanner:

```bash
# Smoke — quick socket count
python3 tools/quality/closure_debt_crawler.py \
  --root lean --limit 50 --print-progress \
  --json-out reports/audit/mission-smoke.json \
  --md-out  reports/audit/mission-smoke.md \
  --print-summary

# Full pass on scope (use watchdog)
timeout 300 python3 tools/quality/closure_debt_crawler.py \
  --root lean --print-progress \
  --json-out reports/audit/mission-full.json \
  --md-out  reports/audit/mission-full.md \
  --print-summary
```

Reflect each socket as a SQL todo:

```sql
INSERT INTO todos (id, title, description, status) VALUES
  ('<module>/<DeclarationName>', 'Close debt socket', 'Prove <theorem> in <file>', 'pending');
```

### 2 — Socket Selection (each turn)

Pick the highest-priority open socket:

```sql
SELECT id, title FROM todos WHERE status = 'pending'
ORDER BY CASE
  WHEN title LIKE '%sorry%'    THEN 0   -- P0: sorry holes
  WHEN title LIKE '%Exists%'   THEN 1   -- P1: existence packaging
  ELSE 2                                -- P2: advisory
END
LIMIT 1;
```

If `/mission subgoal` was invoked, that socket is forced next regardless of order.

### 3 — Proof Turn

For the selected socket the agent must:

1. Identify the target theorem statement from the debt label.
2. Find a Mathlib-rooted derivation chain:
   - terminal theorem ← supporting lemmas (same file) ← Mathlib lemmas
   - Document this chain in a comment block above the theorem.
3. Write a full constructive proof (no `sorry`, no opaque witnesses without
   kernel-checked derivation).
4. Run immediate verification:

```bash
lake env lean <file>
```

5. Optionally run `#print axioms <TheoremName>` and confirm no repo-custom admits.

### 4 — Judge Gate

After each proof turn the judge checks (strict order):

| Check | Pass condition |
|-------|---------------|
| **Lean kernel** | `lake env lean <file>` exits 0, no error output |
| **No new witnesses** | Diff contains no new `sorry`, `native_decide` with unknown axiom, or opaque `noncomputable def _ : _ := ⟨...⟩` without proof fields |
| **Derivation chain** | The response documents: target theorem → supporting lemmas → first Mathlib-rooted constants |
| **Debt count delta** | Crawler diff shows ≥1 fewer debt label in the target file |

All four checks must pass for the judge to return `done` on that socket.

If any check fails: return `continue` and feed the **Continuation Prompt**.

The judge never upgrades a partial result: a file that compiles but still
carries the original debt label is `continue`, not `done`.

### 5 — Continuation Prompt Template

```
[Closure Mission Loop — continuing]
Mission scope: {scope}
Current socket: {socket_id} in {file}
Remaining open sockets: {remaining_count}

Last turn result:
  Kernel: {kernel_result}        ← "PASS" | "FAIL: <error excerpt>"
  New witnesses: {witness_check} ← "none" | "BLOCKED: <pattern found>"
  Derivation chain: {chain_check}← "documented" | "MISSING"
  Debt delta: {debt_delta}       ← "-1" | "0 (no progress)" | "BLOCKED"

Policy reminders:
  - No sorry. No opaque witness constructors without a kernel-checked proof term.
  - Every theorem must trace to a Mathlib-rooted constant.
  - Debt label must be removed ONLY after the proof compiles.
  - Prove the socket above. Write the derivation chain comment. Run lake env lean.
  - State explicitly: "Socket <id> closed" or "Blocked: <reason>".
```

### 6 — Loop Exit Conditions

| Condition | Status |
|-----------|--------|
| All SQL todos for the scope are `done` | **Mission done** |
| Turn budget exhausted (default: 30 turns) | **Auto-paused** — resume with `/mission resume` |
| Three consecutive `BLOCKED` verdicts on the same socket | **Auto-paused** — agent must escalate or skip |
| User sends `/mission pause` | **User-paused** |
| Lean toolchain error unrelated to the socket | **Skip socket** → mark `blocked`, move to next |

---

## State Persistence

Mission state is stored in the session SQL `todos` table with status transitions:

```
pending → in_progress → done
                     ↘ blocked
```

On resume, the loop queries:

```sql
SELECT id FROM todos WHERE status IN ('pending', 'in_progress') LIMIT 1;
```

And restores the scope from the session plan file (`~/.copilot/session-state/<id>/plan.md`).

---

## Judge Configuration

The judge for this loop is **not** an auxiliary LLM call.  
It is a deterministic script executed after every proof turn:

```python
# tools/quality/mission_judge.py  (to be created)
#
# Exit codes:
#   0 = DONE (socket closed)
#   1 = CONTINUE (keep working)
#   2 = BLOCKED (auto-pause)
#
# Steps:
#   1. Run `lake env lean <file>`; capture stdout/stderr.
#   2. Check diff for forbidden patterns: sorry, native_decide axiom, opaque witness.
#   3. Run closure_debt_crawler on the file; compare debt count to baseline.
#   4. Check response text for derivation chain comment block.
#   5. Emit verdict JSON: {"done": bool, "reason": str, "checks": {...}}

import subprocess, sys, json, re

FORBIDDEN = [r'\bsorry\b', r'native_decide', r'noncomputable def \w+ : \w+ := ⟨']

def judge(file: str, response: str, baseline_debt: int) -> dict:
    kernel = subprocess.run(
        ['lake', 'env', 'lean', file],
        capture_output=True, text=True
    )
    kernel_pass = kernel.returncode == 0 and 'error' not in kernel.stderr.lower()

    diff_text = response  # agent must include diff or new code in response
    new_witness = any(re.search(p, diff_text) for p in FORBIDDEN)

    # debt count check via crawler (simplified)
    import tools.quality.closure_debt_crawler as cdc
    current_debt = cdc.count_labels_in_file(file)
    debt_reduced = current_debt < baseline_debt

    chain_present = '←' in response or 'Mathlib.' in response or '-- derivation:' in response

    done = kernel_pass and not new_witness and debt_reduced and chain_present
    reason_parts = []
    if not kernel_pass:    reason_parts.append(f"kernel fail: {kernel.stderr[:200]}")
    if new_witness:        reason_parts.append("new witness pattern detected")
    if not debt_reduced:   reason_parts.append("debt count unchanged")
    if not chain_present:  reason_parts.append("derivation chain not documented")

    return {
        "done": done,
        "reason": "; ".join(reason_parts) if reason_parts else "all checks pass",
        "checks": {
            "kernel_pass": kernel_pass,
            "new_witness": new_witness,
            "debt_reduced": debt_reduced,
            "chain_present": chain_present,
        }
    }

if __name__ == '__main__':
    verdict = judge(sys.argv[1], open(sys.argv[2]).read(), int(sys.argv[3]))
    print(json.dumps(verdict))
    sys.exit(0 if verdict["done"] else 1)
```

---

## Integration with Existing Skills

| Skill | Role |
|-------|------|
| `closure-debt-constructive-proof-sop` | Authoritative policy; SOP steps 1–6 apply |
| `hive-goal-loop` | Meta-shell driver (Jungian expansion → Paulian purification → Logos gate) |
| `formalizer_loop` | Per-tactic repair loop inside each proof turn |
| `lean4` | LSP tooling for goal inspection and premise search |
| `pauli-auditor` | Post-mission audit of promoted theorems |

The closure-mission-loop **wraps** all of these: it sets the outer recurrence
boundary and enforces the judge gate. Inner loops (formalizer_loop, lean4 LSP)
operate within a single proof turn.

---

## Subgoal Criteria (added with `/mission subgoal`)

When a user pins a specific theorem:

```
/mission subgoal "prove einsteinAnomaly_eq_zero_iff_projectors_commute in ConformalProjectorCore.lean"
```

The continuation prompt gains an additional mandatory criterion block:

```
Additional criteria (all must be satisfied for DONE):
- 1. einsteinAnomaly_eq_zero_iff_projectors_commute proved in ConformalProjectorCore.lean
      with derivation chain to Mathlib.LinearAlgebra or Mathlib.Analysis.
```

The judge checks that the criterion is satisfied by **specific evidence** in
the response (a proof block excerpt, a `lake env lean` pass line), not by
generic completion claims.

---

## Anti-Patterns (Logos Gate Rejections)

The judge rejects the following even if `lake env lean` passes:

| Pattern | Rejection reason |
|---------|-----------------|
| `sorry` in any new definition | Proof hole — not closure |
| `noncomputable def foo : T := ⟨witness, trivial⟩` | Opaque witness without proof fields |
| `have : _ := Classical.choice _` as terminal step | Non-constructive existence, not a proof |
| Removing the debt label in a comment without a proof | Textual progress only |
| `Nonempty.intro` without downstream elimination | Existence packaging without content |
| `native_decide` with unverified decision procedure | Not Mathlib-rooted |

---

## UTMOST MANDATE

Effective immediately, replacing witness-gated and external-certificate leftovers
with native Lean proofs is the **top-priority mandate**.

- Witness packets, certificate fields, external certificates, and assumption
  interfaces are temporary scaffolding only.
- Every promoted proposition must be discharged by a native Lean derivation
  chain that traces to Mathlib-rooted constants without vacuous packaging.
- `(Native Closure Mandated: Closure Debt)` labels must persist in source
  until the kernel-verified proof term exists.
- **Do not resolve debt with wording.** Progress must be structural.
- **Real progress** = replacing certificate/witness fields with theorem-backed
  native derivations that survive `lake env lean` and `#print axioms`.
