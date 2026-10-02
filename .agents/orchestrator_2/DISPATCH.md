# DISPATCH — orchestrator_2

## Mission
Lead the repository-wide codebase refactoring and CAS O(1) optimization pass to eliminate brute-force tactics (`native_decide`, `simp` storms, `decide`) across the Lean 4 repository, replacing them with O(1) definitional equality (`rfl`) proofs and exact certificates via OpenGauss / CAS.

## Working Directory
`/home/goutev/info-geometry-lean/.agents/orchestrator_2`

## Inputs
- Authoritative User Request: `/home/goutev/info-geometry-lean/.agents/sentinel/ORIGINAL_REQUEST.md`
- Repository rules: `/home/goutev/info-geometry-lean/AGENTS.md`
- Previous explorer survey data: `/home/goutev/info-geometry-lean/.agents/`

## Operating Constraints
1. NEVER run `lake clean` or delete build caches.
2. Sequential build lock required: use `python3 tools/infra/run_locked_lake_build.py` for builds.
3. Subagent sandbox mandate: Subagents must write to sandboxes/new files, never edit owner files blindly.
4. Continuous tracking mandate: Run `git add -A` after every file creation/modification.
5. Keep working memory in `BRIEFING.md` and execution status in `progress.md`.
6. Dispatch subtasks to specialists (explorers, workers, reviewers) in their own subdirectories under `.agents/`.

## 2026-09-21T20:49:56Z

You are orchestrator_2, the Project Orchestrator for this repository-wide optimization pass.

Working directory: /home/goutev/info-geometry-lean/.agents/orchestrator_2
Authoritative Request: /home/goutev/info-geometry-lean/.agents/sentinel/ORIGINAL_REQUEST.md
Repository rules: /home/goutev/info-geometry-lean/AGENTS.md
Your dispatch instructions: /home/goutev/info-geometry-lean/.agents/orchestrator_2/DISPATCH.md

Core Mission:
Scan the repository for computationally expensive brute-force tactics (`native_decide`, heavy `simp` storms, `decide`), use OpenGauss / CAS tools (SageMath/GAP) to generate exact certificates, and replace them with O(1) definitional equality (`rfl`) or structured proofs respecting categorical colimits and repository architecture.

Strict Mandates from AGENTS.md:
- NEVER run `lake clean` or delete build cache (.lake/build).
- Sequential builds only: run builds via `python3 tools/infra/run_locked_lake_build.py`.
- Subagents must write to sandboxes/new files under `.agents/`, not directly modify owner files until validated.
- Continuous tracking mandate: run `git add -A` after every modification.
- Maintain BRIEFING.md and progress.md in your working directory.

Begin Phase 0 discovery and decomposition, dispatch specialist subagents as needed, and report back when the pass is complete.

