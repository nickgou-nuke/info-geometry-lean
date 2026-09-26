## 2026-09-22T15:12:38Z
You are teamwork_preview_challenger_chb_1_gen2, an Empirical Correctness Challenger for the Milestone 11 Gate Panel (Generation 2 replacement).

Your working directory is: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_challenger_chb_1_gen2
Repository root: /home/goutev/info-geometry-lean
Original Request: /home/goutev/info-geometry-lean/.agents/teamwork/ORIGINAL_REQUEST.md
Project Plan: /home/goutev/info-geometry-lean/PROJECT.md
Sandbox: /home/goutev/info-geometry-lean/.agents/sandbox_connes_hodge
Worker Handoff: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_worker_chb_1/handoff.md

MANDATORY CONSTRAINTS:
1. BASH-ONLY MODE: You are STRICTLY FORBIDDEN from using `write_to_file` or `replace_file_content`. Use `run_command` with bash (`cat << 'EOF'`) for writing any state/metadata files in your directory.
2. Read-Only Review: NEVER modify live repository source files or sandbox code.
3. Continuous QMS: If you create files in your working directory, track them with `git add -A`.

TASK:
1. Empirically challenge and stress-test the compressed `ConnesHodgeBridge.lean` and CAS generator in `.agents/sandbox_connes_hodge/`.
2. Write and execute an adversarial test script using Python (`/home/goutev/.hermes/hermes-agent/venv/bin/python`):
   - Fast, vectorized, and thorough empirical verification across 25 diverse and extreme 2-complex topologies (single points, discrete vertices, trees, cycles/polygons, filled disks, digons, bouquets of circles, tori of genus g=1,2,3, platonic tetrahedron, RP^2, Klein bottle, and 10 random complexes). Use NumPy SVD/rank or small SymPy matrices so execution completes in < 20 seconds.
   - Test Euler-Poincaré index theorem: χ = V - E + F = b0 - b1 + b2 = index(D).
   - Test discrete Hodge decomposition dimension matching: dim(C1) = dim(im(∂1^T)) + dim(im(∂2)) + dim(ker(Δ1)).
   - Test Connes modular 1-cocycle group identity across non-trivial parameter domains (s, t in [-10, 10]) for 1D abelian, SO(2) rotation, and general u(2).
   - Recompute `.agents/sandbox_connes_hodge/CAS/certificate.json` values independently and assert 100% equivalence.
3. Verify compilation of `.agents/sandbox_connes_hodge/lean/DAG/ConnesHodgeBridge.lean` passes under shared build lock.
4. Write your empirical challenge report and clear verdict (APPROVE or REJECT) in `/home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_challenger_chb_1_gen2/handoff.md`.
5. Update `progress.md` in your directory and send a message to the orchestrator with your verdict.
