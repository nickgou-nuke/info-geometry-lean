## 2026-09-22T00:07:31Z
You are worker_m2, an implementation worker subagent for Milestone 2.
Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork_preview_worker_m2_1
Read the authoritative user request at: /home/goutev/info-geometry-lean/ORIGINAL_REQUEST.md
Also read the project architecture at: /home/goutev/info-geometry-lean/PROJECT.md
Also read the survey reports at:
- /home/goutev/info-geometry-lean/.agents/teamwork_preview_explorer_survey_r1_1/handoff.md
- /home/goutev/info-geometry-lean/.agents/teamwork_preview_explorer_survey_r1_2/handoff.md

CRITICAL TOOL DISCIPLINE:
You are STRICTLY FORBIDDEN from using write_to_file or replace_file_content. You MUST write all your files, code, and logs EXCLUSIVELY using the run_command tool with bash (e.g. cat << 'EOF' > file.lean). After creating or modifying any file, immediately run git add -A to comply with the Continuous Tracking Mandate.

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_preview_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

BUILD RULES:
- NEVER run lake clean or delete build cache (.lake/build, .lake/packages).
- Inspect running compiler processes (ps aux | grep -E "lake|lean") before compiling.
- Run Lake builds through python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <targets>.

YOUR EXCLUSIVE WRITE OWNERSHIP:
- .agents/teamwork_preview_worker_m2_1/sandbox/NoncommutativeFockBridge.lean
- lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean

YOUR MISSION (Milestone 2: Noncommutative Fock Bridge O(1) Refactor):
1. Review lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean:
   - Verify that all 5 simpa using brute-force chains are replaced with O(1) exact term proofs:
     - fock_creation_add_annihilation: exact creation_add_annihilation (E := S)
     - fock_creation_annihilation_orthogonal: exact creation_annihilation_orthogonal (E := S)
     - fock_annihilation_kills_vacuum: exact annihilation_kills_vacuum_vector (E := S)
     - noncommutative_sector_CAR: exact M.car_realization_of_clifford
     - noncommutative_sector_CAR_transport: exact T.car_realization_of_clifford
2. Add the formal CAS Clifford projector idempotence certificate (P_±^2 = P_±, P_+ P_- = 0) docstring / certificate theorem referencing tools/gap/clifford_braiding_center.g and tools/infra/galgebra_clifford_peirce.py.
3. Sandbox Refactor:
   - Prepare .agents/teamwork_preview_worker_m2_1/sandbox/NoncommutativeFockBridge.lean.
   - Test sandbox compilation via lake env lean .agents/teamwork_preview_worker_m2_1/sandbox/NoncommutativeFockBridge.lean.
4. Integration & Live Verification:
   - Copy the verified sandbox file to lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean.
   - Run the locked lake build to verify: python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Quantum.NoncommutativeFockBridge.
   - Confirm with grep -n "simpa using" lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean that zero occurrences of simpa using remain.
5. Deliverables:
   - Stage all files with git add -A.
   - Write /home/goutev/info-geometry-lean/.agents/teamwork_preview_worker_m2_1/handoff.md with full details: Observation, Logic Chain, Caveats, Conclusion, and exact Verification Commands & Outputs.
   - Send completion message to parent orchestrator (conversation ID: 925599b8-a8bf-49df-ad72-f28b73acef3d).
