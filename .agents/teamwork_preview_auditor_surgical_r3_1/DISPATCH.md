## 2026-09-22T04:19:04Z
You are auditor_surgical_r3_1, a teamwork_preview_auditor subagent.
Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork_preview_auditor_surgical_r3_1/
Your parent orchestrator is: orchestrator_4 (Conversation ID: 2721f54e-272c-4343-a56a-c83316b51e77).

MANDATORY FIRST STEP:
Read the authoritative user request at /home/goutev/info-geometry-lean/.agents/ORIGINAL_REQUEST.md.
Also read candidate file:
/home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean
and live file:
/home/goutev/info-geometry-lean/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean

CRITICAL CONSTRAINTS:
- BASH-ONLY MODE: You are STRICTLY FORBIDDEN from using write_to_file or replace_file_content. Use run_command with bash for ALL file writes.
- Continuous Git Tracking: Run `git add -A` immediately after creating or modifying any file.
- Safe Lake Build: NEVER run `lake clean` or delete build cache. Run locked commands via `tools.build_lock`.

TASK & FORENSIC AUDIT SCOPE:
Execute rigorous forensic integrity verification:
1. Token Forensics:
   Verify strictly 0 occurrences of `native_decide`, 0 `simpa using`, 0 `sorry`/`admit` in the candidate file.
2. Axiomatic Integrity:
   Run Lean code to print axioms for the declared theorems (e.g. `case1Border_isMoorePenrose`, `case1Schur_isMoorePenrose`, `case3Border_isMoorePenrose`, `case3Schur_isMoorePenrose`, `case1_conjugated_border_isMoorePenrose`).
   Confirm strictly 0 occurrences of `Lean.ofReduceBool` (untrusted VM axiom) and 0 occurrences of `sorryAx`.
   Verify dependencies are strictly on foundational Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).
3. Proposition Fidelity Forensics:
   Diff the theorem statements of all 24 declarations between candidate and live git HEAD to guarantee zero signature tampering.
4. CAS Script Execution & JSON Verification:
   Execute `python3 .agents/sandbox_surgical_o1/CAS/cas_moore_penrose_certificate.py` and inspect `moore_penrose_certificates.json`. Confirm exact symbolic match.
5. Record your verdict (CLEAN or INTEGRITY VIOLATION) in your handoff report:
   `/home/goutev/info-geometry-lean/.agents/teamwork_preview_auditor_surgical_r3_1/handoff.md`.
6. Notify orchestrator via send_message with your verdict and handoff path.
