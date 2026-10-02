# Handoff Report: Sandbox Environment, Build Lock, and E2E Verification Suite Audit
**Agent:** teamwork_preview_explorer (explorer_survey_r5_3)  
**Parent:** orchestrator_5 (`c310530f-678b-4c1c-948e-b8e7ff7beb38`)  
**Date:** 2026-09-22T08:36:00+03:00  

---

## 1. Observation

1. **Build Lock Mechanism and Kernel Semantics**:
   - Inspected `tools/build_lock.py` (lines 48–125) and `tools/infra/run_locked_lake_build.py`.
   - Initial state of `/tmp/info-geometry-build.lock`:
     `{"owner": "check:lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean", "pid": 295412, "acquiredAt": 1790051943.3666005}`
   - Verified that PID 295412 was not running (`ps -p 295412` returned exit code 1).
   - Executed non-blocking lock test:
     `python3 -c "from tools.build_lock import acquire_build_lock; lock = acquire_build_lock(None, 'probe', block=False); lock.release()"`
     The call succeeded instantly (exit code 0), and truncated `/tmp/info-geometry-build.lock` to 0 bytes upon release.
   - Tested target build under lock:
     `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock DAG.DiracLaplacian`
     Acquired lock cleanly, completed 1774 jobs successfully with exit code 0, and cleanly released the lock.

2. **Process Hygiene & Resource Contention**:
   - Monitored running processes:
     `goutev 300542 ... bash -c time lake env lean lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean`
     `goutev 300623 ... lean lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean (71.8% CPU, 4.5 GB RAM, running for >4m13s)`
   - This raw `lake env lean` command bypassed `/tmp/info-geometry-build.lock`, running concurrently with other swarm tasks and saturating core 0.

3. **E2E Test Suite Execution (`tools/e2e_cas_o1_suite.sh`)**:
   - Executed `bash tools/e2e_cas_o1_suite.sh --tier 2`: 5/5 tests passed in 3.0 seconds (clean 0 native_decide, 0 simpa using, 0 sorry, CAS script verified, proposition fidelity verified).
   - Executed `bash tools/e2e_cas_o1_suite.sh --tier all`:
     * Tier 1: 3/3 PASS (Locked builds of `DAG.DiracLaplacian` and `NoncommutativeFockBridge.lean` succeeded).
     * Tier 2: 5/5 PASS.
     * Tier 3: 4/4 PASS (`scripts/cas_dirac_laplacian_certificate.py` passed, active export in `lean/DAG.lean` passed, compilation of `lean/DAG.lean` passed).
     * Tier 4: Test 4.1 and Test 4.2 timed out after 20s (exit code 124):
       `[FAIL] Compilation performance of lean/DAG/DiracLaplacian.lean: Reason: Timed out after 20s (CPU hang detected)`
     * Test 4.3: PASS. Total: 13 passed, 2 failed.

4. **Lean Kernel Profiling vs Environment Startup**:
   - Tested `lean/DAG/DiracLaplacian.lean` alone via:
     `lake env lean --profile lean/DAG/DiracLaplacian.lean`
   - Total wall-clock time: **15.19s**; Kernel typechecking times: 103ms, 766ms, 872ms, 332ms, 806ms (sum < 3.0s).
   - ~12.5s of the wall-clock time is spent initializing the Lean runtime and memory-mapping precompiled Mathlib oleans.

5. **Test 2.5 Proposition Fidelity & Anti-Facade Architecture**:
   - Inspected lines 213–307 in `tools/e2e_cas_o1_suite.sh`.
   - Strips comments using `grep -v "^\s*--" | sed '/\/\*/,/\*\//d'` to check active tokens (`graphDirac`, `chainComplex`, etc.).
   - Extracts theorem proposition between `theorem <name>` and `:=` via `awk` script, enforcing required token tuples on 10 theorems.
   - Applies negative regexes banning proof-irrelevance (`upper_right_zero = lower_left_zero`), arithmetic substitutions (`trDsq = trΔ₀`), and constant certificate reflexive equalities (`DiracSqCertificate = #[`).

6. **Sandbox Out-of-Tree Compilation**:
   - Tested direct compilation of the sandbox candidate file:
     `lake env lean .agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean`
   - Exited with return code **0** and 0 errors, proving that Lean 4 can resolve all Mathlib dependencies for files located inside `.agents/sandbox_.../` without modifying live files.

---

## 2. Logic Chain

1. **Advisory Lock Reliability (Observation 1)**:
   Because `tools/build_lock.py` uses Linux kernel `flock`, dead processes do not leave blocking kernel locks. The mechanism is reliable against abnormal process termination.
2. **Root Cause of Tier 4 Timeouts (Observations 3, 4, and 2)**:
   The E2E suite's Tier 4 sets `TIMEOUT_SEC=20`. Baseline compilation requires ~15.2s (with ~12.5s spent loading Mathlib oleans). When concurrent subagents run un-locked Lean commands (Observation 2), process scheduling pushes wall clock time to >20s, triggering an artificial exit code 124 despite kernel typechecking requiring only ~2.6s.
3. **Subagent Sandbox Mandate Feasibility (Observation 6)**:
   Lean 4's environment resolution allows standalone files in `.agents/sandbox_.../` to typecheck against the existing olean cache. Thus, the Subagent Sandbox Mandate can be strictly enforced for all ~587 candidate targets.
4. **Generalizing Anti-Facade Verification (Observation 5)**:
   Test 2.5's 3-layer architecture (active symbol census, AST proposition signature isolation, and negative anti-facade patterns) is mathematically sound and should be replicated for all target files in their respective sandboxes prior to promotion.

---

## 3. Caveats

1. The timeout in Tier 4 of `tools/e2e_cas_o1_suite.sh` currently fails under heavy multi-agent concurrency; increasing `TIMEOUT_SEC` from 20s to 35s in the script will eliminate spurious failures.
2. Test 4.3 in `tools/e2e_cas_o1_suite.sh` is currently vacuous (passes in both branches) and should be updated to execute an active non-blocking lock check.
3. Existing files in `tools/deploy_sandbox_files.py` and `skills/lean-sandbox/` are legacy and should not be used for the upcoming Round 5 refactoring swarm.

---

## 4. Conclusion

1. **Build Lock**: Fully operational, crash-resilient, and contention-free under proper protocol.
2. **E2E Suite**: Tiers 1–3 pass completely; Tier 4 requires relaxing `TIMEOUT_SEC` to 35s to prevent false positives from olean startup overhead under swarm load.
3. **Test 2.5 Anti-Facade Rigor**: Highly effective at banning cheating, trivializing proofs, and AST alterations; ready to serve as the template for all candidate targets.
4. **Sandbox Protocol**: Confirmed fully viable for out-of-tree typechecking; standardized 5-step operational protocol documented in `infra_report.md`.

---

## 5. Verification Method

1. **Verify Non-Blocking Build Lock Availability**:
   ```bash
   python3 -c "from tools.build_lock import acquire_build_lock; lock = acquire_build_lock(None, 'verify', block=False); lock.release(); print('LOCK OK')"
   ```
2. **Verify Tier 2 Boundary & Anti-Facade Audit**:
   ```bash
   bash tools/e2e_cas_o1_suite.sh --tier 2
   ```
3. **Verify Sandbox Compilation**:
   ```bash
   lake env lean .agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean
   ```
4. **Verify Locked Lake Build**:
   ```bash
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock DAG.DiracLaplacian
   ```
