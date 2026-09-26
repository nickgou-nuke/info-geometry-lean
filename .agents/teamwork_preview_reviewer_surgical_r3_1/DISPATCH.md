## 2026-09-22T04:19:03Z
You are reviewer_surgical_r3_1, a teamwork_preview_reviewer subagent.
Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork_preview_reviewer_surgical_r3_1/
Your parent orchestrator is: orchestrator_4 (Conversation ID: 2721f54e-272c-4343-a56a-c83316b51e77).

MANDATORY FIRST STEP:
Read the authoritative user request at /home/goutev/info-geometry-lean/.agents/ORIGINAL_REQUEST.md.
Also read:
- Master specification: /home/goutev/info-geometry-lean/PROJECT.md
- Worker handoff: /home/goutev/info-geometry-lean/.agents/teamwork_preview_worker_surgical_o1/handoff.md
- Candidate Lean file: /home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean
- Original live file: /home/goutev/info-geometry-lean/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean
- Patch: /home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/diffs/candidate.patch

CRITICAL CONSTRAINTS:
- BASH-ONLY MODE: You are STRICTLY FORBIDDEN from using write_to_file or replace_file_content. Use run_command with bash (cat << 'EOF', sed, echo) for ALL file writes.
- Continuous Git Tracking: Run `git add -A` immediately after creating or modifying any file.
- Safe Lake Build: NEVER run `lake clean` or delete build cache. Run single-file check using locked runner:
  python3 -c "
  import sys, subprocess
  from tools.build_lock import acquire_build_lock
  target_file = sys.argv[1]
  with acquire_build_lock(None, f'review-check:{target_file}', block=True):
      res = subprocess.run(['lake', 'env', 'lean', target_file])
      sys.exit(res.returncode)
  " "<candidate_file>"

TASK & REVIEW SCOPE:
1. Examine code quality, correctness, and completeness of all 24 declarations in the candidate file.
2. Verify 100% proposition fidelity against the live file: every theorem name, signature, and proposition statement must match verbatim.
3. Verify that all 26 `native_decide` occurrences have been eliminated without introducing `simpa using`, `sorry`, or `admit`.
4. Compile the candidate file using the locked runner snippet. Confirm exit code 0 and zero warnings.
5. Record your verdict (APPROVE or REQUEST_CHANGES) with supporting evidence in your handoff report:
   `/home/goutev/info-geometry-lean/.agents/teamwork_preview_reviewer_surgical_r3_1/handoff.md`.
6. Notify orchestrator via send_message with your verdict and handoff path.
