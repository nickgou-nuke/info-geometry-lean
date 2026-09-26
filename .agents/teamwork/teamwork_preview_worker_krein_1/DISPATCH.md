## 2026-09-22T13:13:05Z

You are teamwork_preview_worker_krein_1, a Surgical Compression Worker for Milestone 10: KreinAttentionEnergy Compression.

Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_worker_krein_1
Repository root: /home/goutev/info-geometry-lean
Original Request: /home/goutev/info-geometry-lean/.agents/teamwork/ORIGINAL_REQUEST.md
Project Plan: /home/goutev/info-geometry-lean/PROJECT.md
Sandbox Directory: /home/goutev/info-geometry-lean/.agents/sandbox_krein

Explorer Handoff Reports to Read:
- /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_krein_1/handoff.md
- /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_krein_2/handoff.md
- /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_krein_3/handoff.md

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

MANDATORY CONSTRAINTS:
1. BASH-ONLY MODE: You are STRICTLY FORBIDDEN from using `write_to_file` or `replace_file_content`. You MUST use `run_command` with bash (`cat << 'EOF'`) for ALL file writes.
2. SUBAGENT SANDBOX MANDATE: NEVER touch or modify live repository files (e.g. `lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`). ALL work must be written, generated, and compiled inside `.agents/sandbox_krein/`.
3. QMS Protocol: Continuously stage your created files with `git add -A`.
4. Sequential Build Locking: Respect the shared build lock via `tools/infra/run_locked_lake_build.py` or inspect running processes before executing compiler commands. NEVER execute `lake clean`.
5. Python SymPy Environment: Use `/home/goutev/.hermes/hermes-agent/venv/bin/python` to run Python CAS scripts with SymPy.

DETAILED WORKER TASKS:
1. Read the 3 explorer handoff reports.
2. Verify/run `.agents/sandbox_krein/CAS/cas_krein_attention_certificate.py` and ensure `.agents/sandbox_krein/CAS/certificate.json` is generated.
3. Write the compressed Lean 4 file at `.agents/sandbox_krein/lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`:
   - Prune unused `import InfoGeometry.Algebra.FiniteSpinAlgebra`.
   - `kreinInteractionEnergy_eq_neg_splitB11` proven by `rfl` (0 tactics).
   - `kreinAttentionWeights_sum_one` proven by term witness `attentionWeights_sum_one q ctx splitB11 β` (0 tactics, eliminating `simpa using`).
   - Preserve all original public declarations and attributes (`@[simp, rep_depth krein]`, `@[rep_depth thermo]`).
4. Verify compilation of the sandbox file:
   Check running processes (`ps aux | grep lake`), acquire build lock if needed, and run:
   `lake env lean --threads 1 .agents/sandbox_krein/lean/InfoGeometry/LLM/KreinAttentionEnergy.lean`
   Ensure clean compilation with 0 errors, 0 warnings, 0 `sorry`, 0 `native_decide`, 0 `simpa using`.
5. Generate unified diff against live file:
   `diff -u lean/InfoGeometry/LLM/KreinAttentionEnergy.lean .agents/sandbox_krein/lean/InfoGeometry/LLM/KreinAttentionEnergy.lean > .agents/sandbox_krein/diffs/krein_attention_energy.diff`
6. Create verification audit in `.agents/sandbox_krein/audit/verification_report.md`.
7. Stage all changes with `git add -A`.
8. Write `progress.md` and `handoff.md` in your working directory `/home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_worker_krein_1/` following the Handoff Protocol (Observation, Logic Chain, Caveats, Conclusion, Verification Method).
9. Send a message to the orchestrator reporting your completion.
