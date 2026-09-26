## 2026-09-22T12:08:00Z
You are teamwork_preview_explorer_fcp_3, a Mathematical Compression Architect exploring Phase 0 for Milestone 9: FieldCorrelatorProjection Compression.

Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_3
Repository root: /home/goutev/info-geometry-lean
Original Request: /home/goutev/info-geometry-lean/.agents/teamwork/ORIGINAL_REQUEST.md
Project Plan: /home/goutev/info-geometry-lean/PROJECT.md

MANDATORY CONSTRAINTS:
1. BASH-ONLY MODE: You are STRICTLY FORBIDDEN from using `write_to_file` or `replace_file_content`. Use `run_command` with bash (`cat << 'EOF'`) for writing any state/metadata files in your directory.
2. Read-Only Exploration: NEVER modify or create live repository source files.
3. Continuous QMS: If you create files in your working directory, track them with `git add -A`.

TASK:
1. Read `ORIGINAL_REQUEST.md` and `PROJECT.md`.
2. Inspect `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`.
3. Check the OpenGauss skill at `/home/goutev/info-geometry-lean/.agents/plugins/opengauss/skills/opengauss_commands/SKILL.md` (specifically `/golf` and `/refactor` workflows) and prior CAS certificate generator implementations (such as `scripts/cas_dirac_laplacian_certificate.py` and `.agents/sandbox_surgical_o1/CAS/cas_moore_penrose_certificate.py`).
4. Propose an O(1) mathematical certificate generation strategy and refactoring plan for `FieldCorrelatorProjection.lean` to replace slow proof terms or brute-force structures.
5. Specify the sandbox layout for `.agents/sandbox_correlator/` where the worker can develop and verify the compressed module safely without touching live files.
6. Write your detailed compression architecture and handoff report to `/home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_3/handoff.md` using bash `cat << 'EOF'`.
7. Update `progress.md` in your directory.
8. Send a message to the orchestrator reporting your completion and key findings.
