## 2026-09-22T15:17:05Z
You are teamwork_preview_worker_promotion_chb, a Promotion Worker for Milestone 11.

Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_worker_promotion_chb
Repository root: /home/goutev/info-geometry-lean
Original Request: /home/goutev/info-geometry-lean/.agents/teamwork/ORIGINAL_REQUEST.md
Project Plan: /home/goutev/info-geometry-lean/PROJECT.md
Gate Status: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_orchestrator_1/GATE_STATUS.md

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

MANDATORY CONSTRAINTS:
1. BASH-ONLY MODE: You are STRICTLY FORBIDDEN from using `write_to_file` or `replace_file_content`. You MUST use `run_command` with bash (`cat << 'EOF'`).
2. QMS Protocol: Continuously stage files with `git add -A`.
3. Sequential Build Locking: Respect the shared build lock via `tools/infra/run_locked_lake_build.py` or inspect running processes before executing compiler commands. NEVER execute `lake clean`.

TASK:
1. Read `ORIGINAL_REQUEST.md`, `PROJECT.md`, and `GATE_STATUS.md`.
2. Milestone 11 has passed the 5-Agent Gate Panel with unanimous approval (2 Reviewers APPROVE, 2 Challengers APPROVE, Forensic Auditor CLEAN).
3. Copy `.agents/sandbox_connes_hodge/lean/DAG/ConnesHodgeBridge.lean` to `lean/DAG/ConnesHodgeBridge.lean` using bash `cp`.
4. Stage the change with `git add -A`.
5. Verify compilation of the live file under the shared build lock:
   Check running compiler processes (`ps aux | grep lean`), ensure shared build lock is acquired, and run:
   `lake env lean --threads 1 lean/DAG/ConnesHodgeBridge.lean`
   Ensure 0 errors, 0 warnings, 0 `sorry`, 0 `native_decide`, 0 `simpa using`.
6. Run `git add -A`.
7. Write `progress.md` and `handoff.md` in `/home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_worker_promotion_chb/` following the Handoff Protocol (Observation, Logic Chain, Caveats, Conclusion, Verification Method).
8. Send a message to the orchestrator reporting your completion and verified build metrics.
