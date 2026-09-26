## 2026-09-22T15:20:16Z
You are teamwork_preview_worker_e2e_verification, an E2E Verification Worker for Milestone 12.

Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_worker_e2e_verification
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
2. Conduct global end-to-end verification across the 3 compressed bottleneck modules and their key consumers:
   - Target 1: `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`
   - Target 2: `lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`
   - Target 3: `lean/DAG/ConnesHodgeBridge.lean`
   - Consumer: `lean/DAG.lean`
3. Under shared build lock `/tmp/info-geometry-build.lock` (using `tools/build_lock.py` or inspecting running compiler processes):
   Run single-threaded Lean compiler verification:
   `lake env lean --threads 1 lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`
   `lake env lean --threads 1 lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`
   `lake env lean --threads 1 lean/DAG/ConnesHodgeBridge.lean`
   `lake env lean --threads 1 lean/DAG.lean`
4. Verify that for every target:
   - Return code == 0
   - Compiler errors count == 0
   - Compiler warnings count == 0
   - Cheat tokens count == 0 (`sorry`, `native_decide`, `simpa using`, `admit`)
   - Axiom check: only standard Lean core axioms (`[propext, Classical.choice, Quot.sound]`)
5. Verify that all 3 CAS certificates exist and are valid:
   - `.agents/sandbox_correlator/CAS/certificate.json`
   - `.agents/sandbox_krein/CAS/certificate.json`
   - `.agents/sandbox_connes_hodge/CAS/certificate.json`
6. Run `git add -A`.
7. Write `progress.md` and `handoff.md` in `/home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_worker_e2e_verification/` following the Handoff Protocol (Observation, Logic Chain, Caveats, Conclusion, Verification Method).
8. Send a message to the orchestrator reporting your completion and verified metrics.
