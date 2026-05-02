# Context Pack: Sinkhorn Defect Flow & LLM Thermodynamics

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

## Terminology Map

| Alias/Term | Canonical Symbol / Owner Concept |
|------------|----------------------------------|
| LLM Softmax | `gibbsWeight` (Gibbs distribution of Grand Canonical ensemble) |
| Attention Weights | `attentionWeights` (normalized thermodynamic state) |
| MoE Router Output | `normalizedMixture` (gauge-fixed convex combination) |
| Unnormalized Weights | `unnormalizedWeights` (pre-quantum measure $e^{-\beta E}$) |
| Partition Function | `routerPartition` (gauge scale factor) |
| Sinkhorn Step | `rowNormalize` / `colNormalize` (Weyl gauge transforms) |
| Radon-Nikodym Barrier | `phaseRNBarrierBefore` / `δ_relVol` |
| Router Defect | `δ_odd` (odd-sector defect functional) |

## Proved Core & Boundaries

**What is proven (Audit Green / No Axiom Holes):**
1. **Thermodynamic Attention:** Softmax attention is not merely biomimicry; it is formally proven to be the Gibbs distribution of a Grand Canonical ensemble (`Attention.lean`).
2. **MoE as Gauge Theory:** Mixture of Experts (MoE) is modeled as a thermodynamic gauge theory. Unnormalized router logits are the pre-quantum measure, and normalization (softmax) is rigorous gauge fixing (`MixtureOfExperts.lean`).
3. **Sinkhorn as Weyl Gauge Transform:** The iterative Sinkhorn-Knopp algorithm is proven to be an alternating sequence of left/right diagonal Weyl gauge transforms that monotonically minimize the Radon-Nikodym barrier (`SinkhornFoundation.lean`).
4. **The Defect Bridge:** The residual error in an LLM MoE router is formally bridged to the canonical "non-equilibrium clock defect" from the deep physical theory (`SinkhornDefectFlow.lean`).

## Open Gaps & Socratic Prompts

While the structural isomorphism between LLM routing and thermodynamic phase space is proven, the *dynamical consequences* of the defect flows remain open for exploration.

### 1. The Clock Defect & Attention Decay
> **Prompt:** We have proven that the MoE router residual equals the canonical non-equilibrium clock defect (`residual_eq_clockDefect`). If the router fails to reach detailed equilibrium (`δ_odd > 0`), what is the precise impact on the downstream `attentionWeights`? Does a persistent clock defect force a specific decoherence rate in the attention mechanism?

### 2. Triality & The Operator Cut
> **Prompt:** In `TrialityMoE.lean`, we prove that the `sourcedGenerator` of the router commutes with the Drazin spectral projector (`sourcedGenerator_respects_cut`). Does this imply that the "inactive" experts (those gated to 0) still leave a topological trace in the complementary spectral subspace? How can we measure the "ghost" of an unrouted expert?

### 3. Emergent Time from Sinkhorn Steps
> **Prompt:** `CountSinkhornFlow.lean` defines `countInducedSinkhornTrajectory` as an emergent time flow. In the context of an actual transformer forward pass, do the discrete layers of the network correspond to these Sinkhorn normalization steps? If so, is depth in a neural network mathematically identical to the flow of thermodynamic time?

### 4. Bekenstein Bound on Context Windows
> **Prompt:** We have the `BekensteinBound.lean` and `Attention.lean` (which defines the Context Window). If attention is a thermodynamic state, what is the Bekenstein bound on the context window? Is there a rigorous proof that context length is fundamentally bounded by the available thermodynamic free energy of the token state space?
