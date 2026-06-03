# Agent Skill Distribution

The canonical SOP for graph-guided Lean redundancy cleanup lives at:

```text
skills/lean-dag-wire-refactor/SKILL.md
```

All agent-specific files should be thin adapters pointing to that file. Do not
paste the full workflow into every prompt; token-limited agents should load the
full skill only when the task is actually a DAG/Arango/LeanTrail refactor.

## Local sync

Run:

```bash
python3 tools/agents/sync_lean_dag_wire_refactor_skill.py
```

This syncs the skill to:

- `~/.codex/skills/lean-dag-wire-refactor/SKILL.md`
- `~/.gemini/skills/lean-dag-wire-refactor/SKILL.md`
- `~/.gemini/antigravity/skills/lean-dag-wire-refactor/SKILL.md`
- `~/.openclaw/plugin-skills/lean-dag-wire-refactor/SKILL.md`
- `.gemini/skills/lean-dag-wire-refactor/skill.md`
- `.agents/workflows/lean-dag-wire-refactor.md`
- `.opencode/lean-dag-wire-refactor.md`
- `.github/agents/lean-dag-wire-refactor.agent.md`

## Agent routing

Use agents by role:

- **Codex / Pi via Codex harness:** owner edits, Lean checks, commits, careful repo surgery.
- **OpenClaw:** orchestration, browser, sessions, schedules, cross-agent handoff.
- **Hermes / local agents:** long-running scans, report generation, candidate queue building.
- **GitHub Copilot coding agent:** PR-scoped application of a prepared candidate dossier.
- **Gemini / Antigravity:** deprecated for authority, still useful for proposal-only review.
- **OpenCode:** cheap local implementation passes using the `.opencode` pointer.

## Handoff prompt

```text
Use the lean-dag-wire-refactor SOP.
Read skills/lean-dag-wire-refactor/SKILL.md.
Do not treat graph evidence as proof.
Produce a candidate dossier first.
Do not edit Lean source until the owner file and validation target are known.
```

For LeanTrail surgery planning, agents must run the kernel-backed biopsy stream
before planning:

```bash
lake script run leantrailVacuityAudit
lake script run leantrailVacuityIngest
lake script run leantrailSurgeryPlan
```

If `surgery_plan_report.json` says `vacuity_evidence_nodes: 0`, the planner was
given a plain graph snapshot. The planner fails by default in this state. Use
`--allow-unaudited-snapshot` only for diagnostics; never treat zero surgery
packets from an unaudited snapshot as a cleanup verdict.

## Token policy

Send the full `SKILL.md` only to agents that need to act. Send the short pointer
above to agents that only need to propose candidates or triage evidence.
