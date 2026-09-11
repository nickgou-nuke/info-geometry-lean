# Lean Zulip Community Post: Research-Grade Non-Commutative Benchmark for AlphaProof & RL Engines

**Stream**: `#machine learning for theorem proving`  
**Topic**: Non-Commutative Inductive Colimits & Neutral Hodge Geometry as an Out-of-Distribution Benchmark

Hi all,

With the community celebrating AlphaProof's results on IMO math and the rapid scaling of RL search loops within the Lean 4 compiler, we wanted to share a research-grade structural benchmark exploring non-standard search-tree topologies:

**Repository**: [nickgou-nuke/info-geometry-lean](https://github.com/nickgou-nuke/info-geometry-lean)  
- **11,970+ declarations** verified in Lean 4.28.1 / Mathlib.
- **0 sorry, 0 admit, 0 custom axioms** (`[propext, Classical.choice, Quot.sound]`).
- **Domain**: Information geometry, $C^*$-algebra direct inductive colimits ($\mathcal{O}_n$), Drazin Jordan-Chevalley spectral splittings ($A = A_s + A_n$), and para-complex neutral-signature Lagrangian geometry.

Unlike discrete contest math where tactics like `linarith`, `omega`, and `ring` frequently close goals, higher-level mathematical physics requires navigating:
1. Infinite tensor tower inductive colimits without classical measure-theoretic crutches.
2. Nilpotent operator kernels where associative rewriting tactics fail without specific structural brackets.
3. Totally isotropic Lagrangian subspace projections ($B(P_\pm x, P_\pm y) = 0$).

We have outlined 3 open challenge frontiers specifically designed to test policy/value network exploration on non-standard algebraic spaces:
[DeepMind AlphaProof Dispatch Specification](https://github.com/nickgou-nuke/info-geometry-lean/blob/main/tools/community-outreach/drafts/deepmind_alphaproof_dispatch.md)

Feedback and experiment proposals from the formal math and ML community are warmly welcome!
