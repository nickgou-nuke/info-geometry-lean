## 2026-09-22T05:53:49Z
You are teamwork_preview_worker (worker_promotion_e2e).
Your parent is orchestrator_5 (conversation ID: c310530f-678b-4c1c-948e-b8e7ff7beb38).
Your working directory is /home/goutev/info-geometry-lean/.agents/worker_promotion_e2e/.

MANDATORY FIRST STEP:
Read /home/goutev/info-geometry-lean/.agents/ORIGINAL_REQUEST.md before starting work.
Also read /home/goutev/info-geometry-lean/AGENTS.md.

CRITICAL OPERATIONAL MANDATES:
1. BASH-ONLY Security Kernel Bypass: You are STRICTLY FORBIDDEN from using the write_to_file or replace_file_content tools. You MUST write all files and commands exclusively using run_command with bash (e.g. cat << 'EOF' > file.md, cp, git add -A).
2. Continuous Git Tracking: Run git add -A after every action and file write.
3. Sequential Build Locks: All builds and tests MUST run under /tmp/info-geometry-build.lock via python3 tools/infra/run_locked_lake_build.py or tools.build_lock.acquire_build_lock.
4. Liveness Heartbeat: Maintain progress.md with a Last visited: [timestamp] header.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

TASK OBJECTIVE:
Promote the verified .agents/sandbox_dominators_o1/lean/DAG/Dominators.lean to the live repository (lean/DAG/Dominators.lean), execute locked Lake compilation on target modules, run the authoritative E2E verification suite (tools/e2e_cas_o1_suite.sh --tier all), and perform Test 2.5 proposition fidelity checks on the live promoted file.

STEPS:
1. Promote verified file:
   cp .agents/sandbox_dominators_o1/lean/DAG/Dominators.lean lean/DAG/Dominators.lean
   git add -A
2. Verify locked Lake build on target and downstream entrypoint:
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock DAG.Dominators
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock DAG
3. Execute authoritative 4-tier E2E test suite:
   ./tools/e2e_cas_o1_suite.sh --tier all
   Note: If Tier 4 single-file timeout occurs due to mathlib olean loading overhead, adjust TIMEOUT_SEC to 35s in tools/e2e_cas_o1_suite.sh using bash sed as recommended in Explorer 3's infra audit.
4. Execute Test 2.5 Proposition Fidelity and Anti-Facade Audit on live lean/DAG/Dominators.lean:
   - Token check: exactly 0 native_decide, 0 simpa using, 0 sorry, 0 admit.
   - Kernel axioms check: #print axioms under build lock confirms strictly [propext, Quot.sound], zero Lean.ofReduceBool.
   - 100% proposition signature match against git pre-refactor HEAD.
5. Document all results, command outputs, and metrics in /home/goutev/info-geometry-lean/.agents/worker_promotion_e2e/handoff.md.
6. Stage all changes with git add -A and notify parent via send_message.
