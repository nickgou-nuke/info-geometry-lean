## 2026-09-22T04:27:30Z
Phase 4 Surgical Promotion & E2E Validation:
1. Promote verified candidate to live repository:
   Copy /home/goutev/info-geometry-lean/.agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean
   to /home/goutev/info-geometry-lean/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean using bash cp.
2. Recompile live target under sequential build lock:
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.Hartwig1976SVDMoorePenroseBorder
   Confirm exit code 0 and clean build.
3. Run the authoritative 4-tier E2E test suite:
   ./tools/e2e_cas_o1_suite.sh --tier all
   Verify that all tests across all tiers pass with exit code 0.
4. Verify token elimination on the live file:
   - grep -c "native_decide" lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean must output 0.
   - grep -c "simpa using" lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean must output 0.
   - grep -cE "\b(sorry|admit)\b" lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean must output 0.
5. Verify CAS script execution:
   python3 .agents/sandbox_surgical_o1/CAS/cas_moore_penrose_certificate.py must output exit code 0 and all 7 packets verified.
6. Run git add -A to stage the live file changes and all artifacts.
7. Write comprehensive handoff report to:
   /home/goutev/info-geometry-lean/.agents/teamwork_preview_worker_promotion_e2e/handoff.md.
8. Notify orchestrator via send_message with your findings and handoff path.
