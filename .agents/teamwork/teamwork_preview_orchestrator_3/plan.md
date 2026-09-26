# Plan — OpenGauss Lean 4 Build Repair Swarm

## Objective
Repair Lean 4 build errors under full QMS strict enforcement for:
1. `InfoGeometry.BottPeriodicityReconciliation` (errors regarding `sigma1R`, `sigma3R`, and `ring_nf` failing)
2. `DAG.SearchCoreTests` (verify status/fixes)
3. `DAG.HodgeTheorems` (verify status/fixes)

## Protocol & Guardrails
- **Continuous Git Tracking**: Every file change is immediately staged with `git add -A`.
- **Subagent Sandbox Isolation**: All edits and candidate fixes are written to `.agents/sandbox_bott/` first. Subagents never write to live repo owner files.
- **Zero ctrl+k Deadlock**: Never use `write_to_file` or `replace_file_content`.
- **Zero Bash**: All file reads/writes/operations run via `run_command` with `python3 -c`.
- **OpenGauss Synergy**: Use lean-lsp-mcp tools (`lean_diagnostic_messages`, `lean_goal`, `lean_verify`, etc.) and OpenGauss patterns.
- **Sequential Build Lock**: All lake builds run through `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock`. Never run `lake clean`.

## Milestones
1. **Phase 0 Discovery**:
   - Dispatch Explorers to investigate `InfoGeometry.BottPeriodicityReconciliation`, `DAG.SearchCoreTests`, and `DAG.HodgeTheorems`.
   - Identify exact error line numbers, tactic failures, and required lemma types.
2. **Milestone 1 (Sandbox Implementation & Golf)**:
   - Worker implements fix in `.agents/sandbox_bott/`.
   - Uses OpenGauss `/golf` and `/refactor` to produce clean, small, mathlib-compliant proofs for `sigma1R`, `sigma3R`, and `ring_nf`.
3. **Milestone 2 & 3 (Verification of DAG targets)**:
   - Verify compiler status of `DAG.SearchCoreTests` and `DAG.HodgeTheorems`.
4. **Gate Verification**:
   - Reviewers, Challengers, and Forensic Auditor verify sandbox implementation.
5. **Promotion & Integration**:
   - Orchestrator promotes verified file from sandbox to live repo.
   - Run locked lake build to confirm all targets pass with 0 errors.
