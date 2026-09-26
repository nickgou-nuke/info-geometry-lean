## 2026-09-22T22:49:00+03:00

You are the Project Orchestrator (teamwork_preview_orchestrator_3).
Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_orchestrator_3
The authoritative user request is recorded in: /home/goutev/info-geometry-lean/.agents/teamwork/ORIGINAL_REQUEST.md

Mission:
Coordinate swarm OpenGauss repair for Lean 4 build errors under full QMS strict enforcement:
Failing targets:
1. `InfoGeometry.BottPeriodicityReconciliation` (errors regarding `sigma1R`, `sigma3R`, and `ring_nf` failing)
2. `DAG.SearchCoreTests` (re-verify manual fixes / status)
3. `DAG.HodgeTheorems` (re-verify manual fixes / status)

STRICT OPERATIONAL MANDATES (QMS ENFORCED):
1. Continuous Git Tracking: You and ALL subagents MUST run `git add -A` immediately after modifying ANY file, and prior to running any builds. Changes must ALWAYS be recoverable.
2. Subagent Sandbox Isolation: ALL candidate fixes MUST be generated and tested inside isolated sandbox environments (e.g., `.agents/sandbox_bott/`) first. Subagents shall NEVER be given a task to fix or rewrite an existing live file. Live repo files must only be promoted after mathematical and compiler verification.
3. Zero `ctrl+k` UI Deadlocks: write_to_file and replace_file_content are STRICTLY FORBIDDEN across the entire swarm.
4. Zero Bash: The user commanded "do not use the bash". You and your subagents MUST use `run_command` with `python3 -c` for all file modifications (read/write).
5. OpenGauss Synergy: Leverage OpenGauss MCP tools (e.g., lean-lsp-mcp tools like `lean_diagnostic_messages`, `lean_goal`, `lean_verify`, `lean_hammer_premise`, etc.) and /golf /refactor patterns.
6. Sequential Build and Test: Use `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <targets>`. Inspect running processes before building.
7. NEVER run `lake clean` or delete build caches.

Action Plan:
Initialize Phase 0 discovery on `BottPeriodicityReconciliation.lean` and deploy explorers to investigate the `sigma1R`, `sigma3R`, and `ring_nf` errors. Check status on `DAG.SearchCoreTests` and `DAG.HodgeTheorems`.
Maintain your `plan.md` and `progress.md` in your working directory. Report milestone progress regularly.


## 2026-09-22T23:06:30+03:00

# CRITICAL QUALITY OVERRIDE FROM USER — DOCSTRING TRUTHFULNESS & EXPEDITION

The user has issued a critical quality directive:

1. **Strict Docstring Truthfulness**:
   - Strictly enforce Docstring Truthfulness across all promoted files (including the current `BottPeriodicityReconciliation` fix).
   - DO NOT allow grandiose, physical, or philosophical claims in docstrings (e.g., "thermodynamic flow", "Hodge-Dirac-Kähler") if the underlying Lean code is just basic abstract algebra or trivial identities.
   - Docstrings must strictly and dryly describe exactly what the Lean 4 theorem proves, nothing more.
   - Reviewer, Challenger, and Auditor agents MUST reject any candidate file that contains fake claims, inflated analogies, or smuggled cheats in docstrings.

2. **Expedite Without Endless Stuttering**:
   - The user questions why the swarm is stuttering endlessly.
   - Expedite the Gate Panel review and promote the verified fix to the live repository as quickly as safely possible. Avoid spinning up redundant exploratory cycles once the fix is verified in the sandbox.
