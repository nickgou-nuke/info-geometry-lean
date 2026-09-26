# BRIEFING — 2026-09-21T19:02:00Z

## Mission
Orchestrate OpenGauss CAS golfing to eliminate compiler bottlenecks (simp/decide/native_decide) and replace them with O(1) Sage/GAP CAS certificates in the Lean 4 repository.

## 🔒 My Identity
- Archetype: orchestrator
- Roles: orchestrator, user_liaison, human_reporter, successor
- Working directory: /home/goutev/info-geometry-lean/.agents/orchestrator_1
- Original parent: Sentinel
- Original parent conversation ID: a5012232-4bde-4288-8564-064ae02ce249

## 🔒 My Workflow
- **Pattern**: Project Pattern
- **Scope document**: /home/goutev/info-geometry-lean/PROJECT.md
1. **Decompose**: Survey repository for bottlenecks, CAS tooling, and affected targets; decompose into milestones.
2. **Dispatch & Execute**:
   - **Direct (iteration loop)**: Explorer -> Worker -> Reviewer -> Challenger -> Auditor -> Gate
   - **Delegate (sub-orchestrator)**: Milestone sub-orchestrators for modular execution + E2E Testing Orchestrator
3. **On failure**: Retry -> Replace -> Skip -> Redistribute -> Redesign -> Escalate
4. **Succession**: Threshold 16 spawns; soft handoff to successor.
- **Work items**:
  1. Survey: Map heavy tactics & OpenGauss CAS pipeline [in-progress]
  2. Decomposition & PROJECT.md creation [pending]
  3. Milestone Execution & E2E Testing [pending]
  4. Final Verification & Sentinel Handoff [pending]
- **Current phase**: 0 (Survey)
- **Current focus**: Step 0 Survey (Spawning 3 Explorers)

## 🔒 Key Constraints
- NEVER run lake clean or delete build cache (.lake/build, .lake/packages)
- Sequential build and test mandate (run_locked_lake_build.py)
- Subagent Sandbox Mandate: workers edit new sandbox files, not live owner files directly
- Continuous tracking mandate (git add -A)
- Forensic Auditor verdict is a binary veto (zero tolerance for integrity violations)
- Never reuse a subagent after it has delivered its handoff

## Current Parent
- Conversation ID: a5012232-4bde-4288-8564-064ae02ce249
- Updated: 2026-09-21T19:02:00Z

## Key Decisions Made
- Initializing Project Pattern orchestration.
- Proceeding with Step 0: Survey by spawning 3 Explorers in parallel.

## Team Roster
| Agent | Type | Work Item | Status | Conv ID |
|-------|------|-----------|--------|---------|

## Succession Status
- Succession required: no
- Spawn count: 0 / 16
- Pending subagents: none
- Predecessor: none
- Successor: not yet spawned

## Active Timers
- Heartbeat cron: not started
- Safety timer: none
- On succession: kill all timers before spawning successor
- On context truncation: run `manage_task(Action="list")` — re-create if missing

## Artifact Index
- /home/goutev/info-geometry-lean/.agents/ORIGINAL_REQUEST.md — Authoritative user request
- /home/goutev/info-geometry-lean/.agents/orchestrator_1/DISPATCH.md — Dispatch log
- /home/goutev/info-geometry-lean/.agents/orchestrator_1/progress.md — Liveness & iteration checkpoint
- /home/goutev/info-geometry-lean/PROJECT.md — Master project architecture & milestones (to be created)
