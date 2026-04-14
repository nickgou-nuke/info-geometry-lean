# mcbal Blog Architecture Blocks (Inspiration Library)

This file extracts reusable architecture motifs from the local mcbal post library:

- `external_refs/mcbal_blog/library/posts/*.md`
- `external_refs/mcbal_blog/library/metadata.json`

## Core Blocks

1. Energy-Based Attention Block  
   - Score/energy function over query-context state.
   - Partition function via `logsumexp`.
   - Softmax as Gibbs normalization.
   - Local Lean target: thermodynamic router + simplex certificate.

2. Implicit Attention / Fixed-Point Block  
   - Attention update viewed as one (or few) inference steps in an energy landscape.
   - Supports iterative map interpretation rather than one-shot kernel view.
   - Local Lean target: fixed-point iteration scaffold + Lyapunov/energy descent hypotheses.

3. Spin-Model Transformer Block  
   - Transformer dynamics interpreted as collective spin interaction.
   - Mean-field and free-energy language for layer updates.
   - Local Lean target: triality/split state decomposition with interaction energy surface.

4. Approximate Free-Energy Minimization Block  
   - Layer/router step as minimizing an approximate free-energy objective.
   - Local Lean target: objective decomposition into energy term + entropy term.

5. Entropy Production / Non-Equilibrium Block  
   - Dynamics interpreted through entropy production under non-equilibrium updates.
   - Local Lean target: per-step entropy/production functional and monotonicity statements (assumption-gated).

6. Mixture/Ensemble Effective-Model Block  
   - Attention viewed as implicit mixture of effective energy models.
   - Local Lean target: all-top expert mixture and masked/top-k specializations.

7. Geometric Landscape Visualization Block  
   - Explicit energy landscape framing for interpretability.
   - Local Lean target: energy surface map + update flow representation.

## Immediate Repo Mapping

- `lean/InfoGeometry/LLM/ThermodynamicSwitching.lean`
  - logsumexp partition surface
  - masked/all-top thermodynamic weights
  - simplex-style normalization facts

- `lean/InfoGeometry/LLM/TrialityMoE.lean`
  - active/defect routed split
  - shared+routed decomposition
  - canonical source bridge hooks

- `lean/InfoGeometry/LLM/TransformerArchitecture.lean`
  - Kramers-pair latent lane
  - iRoPE/hyperbolic blend hooks
  - Bogoliubov pair transform interface

- `lean/InfoGeometry/Canonical/GrandCanonicalExperts.lean`
  - bistochastic switch -> permutation-simplex decomposition
  - Clifford-labeled modewise split

- `lean/InfoGeometry/Canonical/ArnoldMajoranaNetwork.lean`
  - Majorana/Bogoliubov transport-preserving expert network theorems

## Suggested Next Formalization Sequence

1. Add a free-energy objective surface in `LLM/ThermodynamicSwitching`.
2. Add an entropy-production per-step functional (bounded/interface layer first).
3. Add fixed-point/implicit attention iteration wrappers.
4. Connect to Arnold-Majorana transport invariants as optional strong hypotheses.

