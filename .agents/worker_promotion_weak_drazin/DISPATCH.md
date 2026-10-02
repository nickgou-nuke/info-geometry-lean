## 2026-09-22T06:19:08Z
You are teamwork_preview_worker (worker_promotion_weak_drazin).
Your parent is orchestrator_5 (conversation ID: c310530f-678b-4c1c-948e-b8e7ff7beb38).
Your working directory is /home/goutev/info-geometry-lean/.agents/worker_promotion_weak_drazin/.

MANDATORY FIRST STEP:
Read /home/goutev/info-geometry-lean/.agents/ORIGINAL_REQUEST.md before starting work.
Also read /home/goutev/info-geometry-lean/AGENTS.md.

CRITICAL OPERATIONAL MANDATES:
1. BASH-ONLY Security Kernel Bypass: You are STRICTLY FORBIDDEN from using the `write_to_file` or `replace_file_content` tools. You MUST write all files and commands exclusively using `run_command` with bash (e.g. `cat << 'EOF' > file.md`, `cp`, `git add -A`).
2. Continuous Git Tracking: Run `git add -A` after every action and file write.
3. Sequential Build Locks: All builds and tests MUST run under `/tmp/info-geometry-build.lock` via `python3 tools/infra/run_locked_lake_build.py` or `tools.build_lock.acquire_build_lock`.
4. Liveness Heartbeat: Maintain `progress.md` with a `Last visited: [timestamp]` header.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

TASK OBJECTIVE:
Promote the verified `.agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` to the live repository (`lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean`), execute locked Lake compilation on `InfoGeometry.Canonical.CampbellMeyerWeakDrazin`, run the authoritative E2E verification suite (`tools/e2e_cas_o1_suite.sh --tier all`), and perform Test 2.5 proposition fidelity checks on the live promoted file.

STEPS:
1. Promote verified file:
   `cp .agents/sandbox_weak_drazin_o1/lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean`
   `git add -A`
2. Verify locked Lake build on target module:
   `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.CampbellMeyerWeakDrazin`
3. Execute authoritative 4-tier E2E test suite:
   `./tools/e2e_cas_o1_suite.sh --tier all`
   Verify all 15 tests pass with exit code 0.
4. Execute Test 2.5 Proposition Fidelity and Anti-Facade Audit on live `lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean`:
   - Token check: exactly 0 `native_decide`, 0 `simpa using`, 0 `sorry`, 0 `admit`.
   - Kernel axioms check: `#print axioms` under build lock confirms strictly `[propext, Classical.choice, Quot.sound]`, with ZERO `Lean.ofReduceBool`.
   - 100% proposition signature match against pre-refactor git HEAD.
5. Document all results, command outputs, and metrics in `/home/goutev/info-geometry-lean/.agents/worker_promotion_weak_drazin/handoff.md`.
6. Stage all changes with `git add -A` and notify parent via `send_message`.
