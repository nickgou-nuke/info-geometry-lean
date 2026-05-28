# Continuous Proof-Cleanup Heartbeat

Goal: clean vacuous Lean content and maintain Mathlib-style, proof-only development.

## Non-negotiables

- Do not add `axiom`, `postulate`, `admit`, or proof-proxy fields.
- Do not hide missing proofs behind witnesses, certificates, laws, assumptions, guards, or reexports.
- If a proof is missing, leave an honest visible `sorry` at the exact theorem.
- Prefer deleting/refactoring vacuous theorem surfaces over preserving wrapper APIs.
- Validate touched Lean files and run the heartbeat after each cleanup.
- Commit and push source changes to both `origin main` and `upstream main`.

## Tick procedure

1. Run:
   ```bash
   python3 tools/quality/proof_heartbeat.py lean/InfoGeometry/Canonical --top 20
   python3 tools/lean4-skills/sorry_analyzer.py lean --format=summary
   ```
2. Select the first real vacuity target from the heartbeat.
3. Inspect semantic usage with `rg`.
4. Make one bounded cleanup:
   - prove from lower real lemmas, or
   - remove/refactor a vacuous proxy surface.
5. Build touched files with `lake env lean <file>`.
6. Run UlamAI checkpoint when practical.
7. Commit and push.
8. Update this file's state block.

## State

- Status: flowing
- Last manual setup: 2026-05-28
- Current scope: `lean/InfoGeometry/Canonical`
- Last proof-cleanup cycle: `2026-05-28T03:07:02Z`
- Current known counts after this cycle: `sorry: 0`, `proxy_field: 160`, `prop_socket: 64`, `reexport_proxy: 115`
- Next target: `lean/InfoGeometry/Canonical/PrimeMBKSelfAdjointTrace.lean` (`finite_to_infinite_limit_law`)
