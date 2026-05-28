---
description: Run one bounded proof-cleanup SOP cycle with the Codex CLI assistant.
argument-hint: '[optional target hint]'
---

# Proof SOP Cycle with Codex

**Input**: $ARGUMENTS

---

## Your Mission

Run exactly one bounded proof-cleanup SOP cycle for this Lean repository using Codex.

This is the bounded inner work unit used by the unbounded cleanup heartbeat. The outer heartbeat may run forever; this command must clean at most one real target, validate it, commit it, and push it.

---

## Phase 1: LOAD - Required Policy Context

Read these files before editing:

```text
HEARTBEAT.md
.agents/workflows/proof_only_sop.md
.agents/workflows/mathlib_rules_sop.md
.agents/workflows/honest_proof_policy.md
external_refs/mathlib_docs/contribute_style.md
skills/proof-only-mandate/SKILL.md
```

Also apply the Mathlib documentation-style rules from the user-provided
Documentation style guidance: module docstrings use `/-!` delimiters on their own
lines, every definition and major theorem should have a `/-- ... -/` docstring,
raw URLs in docs should use angle brackets, sectioning comments should use
module-doc comments, and docstrings should describe mathematical meaning without
overclaiming unproved bridges.

**PHASE_1_CHECKPOINT:**
- [ ] Proof-only policy loaded
- [ ] Honest proof policy loaded
- [ ] Mathlib rules loaded
- [ ] No fake closure permitted

---

## Phase 2: ANALYZE - Find One Real Target

Run:

```bash
python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 20
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
python3 tools/quality/audit_style.py lean/InfoGeometry/Canonical
python3 tools/quality/audit_docstrings.py lean/InfoGeometry/Canonical
```

Select the first real vacuity/proxy target from the heartbeat. Use semantic inspection before editing:

```bash
rg <relevant-symbols> lean/InfoGeometry
lake env lean <candidate-file>
```

**PHASE_2_CHECKPOINT:**
- [ ] One target selected
- [ ] Target is a real proof/proxy cleanup issue
- [ ] Relevant lower lemmas inspected

---

## Phase 3: IMPLEMENT - One Bounded Cleanup

Do exactly one bounded cleanup:

1. prove from real lower lemmas; or
2. delete/refactor a vacuous proxy surface; or
3. if no real proof is available, keep an honest visible `sorry` rather than fake closure.

Never replace missing mathematics with:

```text
witness fields
certificate fields
law fields
assumptions as proof cargo
guards
sockets
reexport wrappers
Prop := True
Nonempty placeholders
axioms/admit
```

Do not stage generated files:

```text
.changes/
artifacts/
reports/
external_refs/
```

**PHASE_3_CHECKPOINT:**
- [ ] At most one bounded cleanup made
- [ ] No hidden proof proxy introduced
- [ ] No generated artifacts staged

---

## Phase 4: VALIDATE - Kernel and Semantic Checks

For every touched Lean file, run:

```bash
lake env lean <file>
```

Then run:

```bash
python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 20
python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
python3 tools/quality/audit_style.py lean/InfoGeometry/Canonical
python3 tools/quality/audit_docstrings.py lean/InfoGeometry/Canonical
```

If useful for the touched file, run Ulam:

```bash
ulam checkpoint <file> --lean-project . --strict --no-allow-axioms
```

**PHASE_4_CHECKPOINT:**
- [ ] Touched Lean files typecheck
- [ ] Sorry analyzer run
- [ ] Heartbeat rerun
- [ ] Mathlib style audit rerun
- [ ] Mathlib documentation audit rerun
- [ ] No axioms/admits/fake closure introduced

---

## Phase 5: COMMIT - Save Source Changes Only

Update `HEARTBEAT.md` State block with timestamp, counts, and next target if that file is part of this cycle.

Stage only source/SOP files changed by this cycle. Never use `git add -A`.

Commit and push:

```bash
git status --porcelain=v1
git add <explicit-files>
git diff --cached --check
git commit -m "<concise proof-cleanup message>"
git push origin main
git push upstream main
```

Write a concise tick summary to:

```text
.archon/task_results/proof-sop-cycle-last.md
```

**PHASE_5_CHECKPOINT:**
- [ ] Only intended source/SOP files staged
- [ ] Commit created
- [ ] Pushed to origin and upstream
- [ ] Tick summary written

## Success Criteria

- **ONE_TARGET_ONLY**: One bounded cleanup was attempted.
- **KERNEL_VALIDATED**: Touched Lean files typecheck.
- **NO_FAKE_PROOF**: No proxy/axiom/admit cargo introduced.
- **SOURCE_COMMITTED**: Intended source changes committed and pushed.
