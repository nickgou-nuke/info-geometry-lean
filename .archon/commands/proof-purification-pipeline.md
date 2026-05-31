---
description: Run the recursive proof purification pipeline with semantic vacuity audit, literature scouting, formalization, and hard proof gates.
argument-hint: '[optional scope overrides]'
---

# Proof Purification Pipeline

**Input**: $ARGUMENTS

---

## Your Mission

Run the recursive purification furnace over the Lean source tree. The pipeline must:
- audit semantic vacuity across the scope,
- discover new vacuity patterns when needed,
- search literature and repo context for genuine proof routes,
- formalize one bounded theorem/debt repair at a time,
- reject proxy-field or witness-pack closure,
- recurse until the debt queue is empty or the user stops it.

## Phase 1: Start the Heartbeat

Run:

```bash
SCOPE=lean \
WORKFLOW=proof-purification-pipeline \
tools/heartbeat/archon_repo_cleanup_loop.sh
```

Use the default unbounded settings unless bounded batch mode is explicitly requested.

## Phase 2: Required Gates

Each tick must include:
- `python3 tools/quality/committed_baseline_gate.py lean --require-pushed`
- `python3 tools/quality/proof_heartbeat.py lean --top 20`
- `python3 tools/quality/semantic_vacuity_gate.py lean --fail-on none --top 50`
- `python3 tools/quality/semantic_content_audit.py --scope all --gate-review`
- commit and push touched files before semantic/proxy audit
- `python3 tools/quality/proof_proxy_diff_gate.py --base <pre-cycle-committed-ref> <scope>`
- `python3 tools/quality/semantic_regression_gate.py --base <pre-cycle-committed-ref> <scope>`
- `lake env lean <touched file>` for each edited Lean file
- `lake build <touched module or package>`

## Phase 3: Expansion Rule

If the semantic audit discovers a new vacuity form:
1. add it to `tools/quality/semantic_vacuity_patterns.json`,
2. rerun the semantic vacuity gate,
3. record the new class in the audit map,
4. continue the recursion.

## Phase 4: Hard Prohibitions

Do not:
- add new `structure`/`class` carriers as proof cleanup,
- add fields to existing structures/classes,
- replace debt with certificates, witnesses, sockets, laws, or readbacks,
- audit or restore uncommitted Lean files,
- stage generated artifacts or reports,
- claim closure without a kernel-checked Lean proof.

## Success Criteria

- semantic vacuity is reduced or explicitly recorded as open debt,
- literature search has produced a genuine proof route when needed,
- Lean files typecheck,
- proof proxy and semantic regression gates pass against committed refs,
- recursion continues until the queue is exhausted.
