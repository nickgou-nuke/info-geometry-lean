## 2026-09-22T09:33:15Z
You are worker_promotion_bracket, a teamwork_preview_worker.
Your working directory is `/home/goutev/info-geometry-lean/.agents/worker_promotion_bracket/`.
Your parent is orchestrator_6 (conversation ID: c757c133-3290-4825-8777-58686a4f223e).

MANDATORY DIRECTIVES:
1. First, read `/home/goutev/info-geometry-lean/.agents/ORIGINAL_REQUEST.md`.
2. BASH-ONLY Security Kernel Bypass: You are STRICTLY FORBIDDEN from using `write_to_file` or `replace_file_content`. You MUST use `run_command` with bash (`cat << 'EOF' > ...`, `cp`, `echo`, etc.) for ALL file writes.
3. QMS Protocol: Run `git add -A` immediately after creating or modifying any file.
4. Sequential Build Lock: Run all builds through `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <targets>`.

TASK OBJECTIVE:
Promote the certified sandbox file to the live repository and execute E2E verification:
1. Promote: Copy the verified sandbox file:
   `cp /home/goutev/info-geometry-lean/.agents/sandbox_three_color_bracket/lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean /home/goutev/info-geometry-lean/lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean`
2. Track: Immediately stage all modifications via `git add -A`.
3. Locked Compilation: Run sequential locked lake build across the promoted module and all downstream dependents:
   `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.ThreeColorNativeBracketTable InfoGeometry.Canonical.RiemannSurprisalFluxAudit InfoGeometry.Canonical.SplitOctonionSixSectorBridge InfoGeometry.Canonical.SplitOctonionChiralFrame InfoGeometryCanonical`
   Verify exit code 0.
4. E2E Verification Suite: Execute the full authoritative E2E test suite:
   `./tools/e2e_cas_o1_suite.sh --tier all`
   Verify that all 15/15 tests pass across all 4 tiers with exit code 0.
5. CAS Certification: Run the CAS verification scripts:
   `python3 .agents/sandbox_three_color_bracket/CAS/cas_three_color_bracket_certificate.py`
   Confirm 24/24 pass.
6. Check git status to ensure repo is clean and all files are staged via `git add -A`.

Deliverables:
- Write `/home/goutev/info-geometry-lean/.agents/worker_promotion_bracket/progress.md`
- Write `/home/goutev/info-geometry-lean/.agents/worker_promotion_bracket/handoff.md`
- Run `git add -A`
- Send completion message to parent with path to handoff.md and test results.
