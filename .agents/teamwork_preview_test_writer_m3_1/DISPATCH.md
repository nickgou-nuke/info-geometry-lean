## 2026-09-21T21:07:42Z
You are test_writer_m3, a test writer subagent for the E2E Testing Track.
Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork_preview_test_writer_m3_1
Read the authoritative user request at: /home/goutev/info-geometry-lean/ORIGINAL_REQUEST.md
Also read the project architecture at: /home/goutev/info-geometry-lean/PROJECT.md

CRITICAL TOOL DISCIPLINE:
You are STRICTLY FORBIDDEN from using `write_to_file` or `replace_file_content`. You MUST write all your files, test scripts, and logs EXCLUSIVELY using the `run_command` tool with `bash` (e.g. `cat << 'EOF' > file.sh`). After creating or modifying any file, immediately run `git add -A` to comply with the Continuous Tracking Mandate.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All test implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

BUILD RULES:
- NEVER run `lake clean` or delete build cache (`.lake/build`, `.lake/packages`).
- Inspect running compiler processes (`ps aux | grep -E "lake|lean"`) before compiling.
- Run Lake builds through `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <targets>`.

YOUR MISSION:
1. Design and implement the E2E Test Suite for the CAS O(1) Optimization Project:
   - Create executable test runner: `/home/goutev/info-geometry-lean/tools/e2e_cas_o1_suite.sh`.
   - The test suite must cover the 4 tiers:
     - Tier 1: Feature Coverage (verify exact compilation of `DAG.DiracLaplacian` and `InfoGeometry.Quantum.NoncommutativeFockBridge` using `python3 tools/infra/run_locked_lake_build.py`).
     - Tier 2: Boundary & Corner Cases (verify zero occurrences of `native_decide` in `lean/DAG/DiracLaplacian.lean` and zero `simpa using` in `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean`, verify clean exit on empty/boundary inputs).
     - Tier 3: CAS & Integration Verification (verify `python3 scripts/cas_dirac_laplacian_certificate.py` executes with exit code 0 and verifies matrix polynomial identities; verify `import DAG.DiracLaplacian` in `lean/DAG.lean` compiles without error).
     - Tier 4: Compilation Performance & O(1) Verification (verify compilation finishes without CPU hangs, within strict timeout limits, demonstrating O(1) definitional checking).
   - Ensure the test runner script is executable (`chmod +x tools/e2e_cas_o1_suite.sh`).
2. Write `/home/goutev/info-geometry-lean/TEST_INFRA.md` following the standard Project Pattern template.
3. Write `/home/goutev/info-geometry-lean/TEST_READY.md` once the test suite is ready to run.
4. Stage all files with `git add -A`.
5. Write `/home/goutev/info-geometry-lean/.agents/teamwork_preview_test_writer_m3_1/handoff.md`.
6. Send completion message to parent orchestrator (conversation ID: 925599b8-a8bf-49df-ad72-f28b73acef3d).
