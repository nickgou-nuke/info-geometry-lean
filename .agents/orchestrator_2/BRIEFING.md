# BRIEFING — 2026-09-21T20:50:00Z

## Mission
Lead repository-wide optimization pass eliminating brute-force tactics (`native_decide`, heavy `simp` storms, `decide`) and replacing with O(1) certificates and definitional equality proofs via OpenGauss/CAS.

## 🔒 My Identity
- Archetype: orchestrator
- Roles: orchestrator, user_liaison, human_reporter, successor
- Working directory: /home/goutev/info-geometry-lean/.agents/orchestrator_2
- Original parent: parent
- Original parent conversation ID: 567a413f-06b0-4b94-b2ac-fa7c883266f6

## 🔒 My Workflow
- **Pattern**: Project Pattern
- **Scope document**: /home/goutev/info-geometry-lean/PROJECT.md
1. **Decompose**: Survey repository for bottlenecks, CAS tooling, and affected targets; decompose into milestones.
2. **Dispatch & Execute**:
   - **Direct (iteration loop)**: Explorer -> Worker -> Reviewer -> Challenger -> Auditor -> Gate
   - **Delegate (sub-orchestrator)**: Milestone sub-orchestrators for modular execution + E2E Testing Orchestrator
3. **On failure**:
   - Retry: nudge stuck agent or re-send task
   - Replace: spawn fresh agent with partial progress
   - Skip: proceed without (only if non-critical)
   - Redistribute: split stuck agent's remaining work
   - Redesign: re-partition decomposition
   - Escalate: report to parent (last resort)
4. **Succession**: Threshold 16 spawns; soft handoff to successor.
- **Work items**:
  1. Survey: Map heavy tactics & OpenGauss CAS pipeline [in-progress]
  2. Decomposition & PROJECT.md creation [pending]
  3. Milestone Execution & E2E Testing [pending]
  4. Final Verification & Completion Report [pending]
- **Current phase**: 0 (Survey)
- **Current focus**: Step 0 Survey (Spawning 3 Explorers)

## 🔒 Key Constraints
- NEVER run lake clean or delete build cache (.lake/build, .lake/packages)
- Sequential build and test mandate (run_locked_lake_build.py)
- Subagent Sandbox Mandate: workers edit new sandbox files under .agents/, not live owner files directly
- Continuous tracking mandate (git add -A)
- Forensic Auditor verdict is a binary veto (zero tolerance for integrity violations)
- Never reuse a subagent after it has delivered its handoff — always spawn fresh
- Top-level Project Orchestrator cannot write source code or explore code directly; delegate everything via invoke_subagent.

## Current Parent
- Conversation ID: 567a413f-06b0-4b94-b2ac-fa7c883266f6
- Updated: 2026-09-21T20:50:00Z

## Key Decisions Made
- Initializing Project Pattern orchestration for repository-wide optimization pass.
- Proceeding with Step 0: Survey by spawning 3 Explorers in parallel.

## Team Roster
| Agent | Type | Work Item | Status | Conv ID |
|-------|------|-----------|--------|---------|
| explorer_survey_1 | teamwork_preview_explorer | Bottleneck identification in Lean files | in-progress | f4c1705a-e122-45cc-b68c-2758c4b47bc7 |
| explorer_survey_2 | teamwork_preview_explorer | OpenGauss & CAS tooling investigation | in-progress | 9ed3852b-a5d4-472f-8d52-ea9716489e1e |
| explorer_survey_3 | teamwork_preview_explorer | Categorical colimit & verification rules | in-progress | 2c6a4b6b-573c-445a-b138-9935ae6efbf4 |

## Succession Status
- Succession required: no
- Spawn count: 3 / 16
- Pending subagents: f4c1705a-e122-45cc-b68c-2758c4b47bc7, 9ed3852b-a5d4-472f-8d52-ea9716489e1e, 2c6a4b6b-573c-445a-b138-9935ae6efbf4
- Predecessor: none
- Successor: not yet spawned

## Active Timers
- Heartbeat cron: task-43 (*/10 * * * *)
- Safety timer: covered by heartbeat cron
- On succession: kill all timers before spawning successor
- On context truncation: run `manage_task(Action="list")` — re-create if missing

## Artifact Index
- /home/goutev/info-geometry-lean/.agents/sentinel/ORIGINAL_REQUEST.md — Authoritative user request
- /home/goutev/info-geometry-lean/.agents/orchestrator_2/DISPATCH.md — Dispatch log
- /home/goutev/info-geometry-lean/.agents/orchestrator_2/progress.md — Liveness & iteration checkpoint
- /home/goutev/info-geometry-lean/PROJECT.md — Master project architecture & milestones
