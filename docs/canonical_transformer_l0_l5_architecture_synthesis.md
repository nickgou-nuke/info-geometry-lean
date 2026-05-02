# Canonical Transformer L0-L5 Architecture

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Date: 2026-04-14

## Objective

This lane is not a replica of industrial transformer internals.
It is a canonical assembly language where transformer morphology is induced by the repository's information-physics spine:

`count -> projective -> operator -> krein -> transport -> thermo`.

The benchmark is therefore architectural ownership, not vendor fidelity.

## Evaluation Rule

A transformer-shaped component is accepted only when:

1. it is owned by a specific `RepDepth`,
2. its bridges are adjacent and lawful,
3. its theorem surface states physical meaning in repo-native language,
4. it composes into an executable dynamics stack without importing external ontology.

## Ownership Matrix

| Component | Owner Surface | `RepDepth` | Physical Meaning | Execution Role |
|---|---|---|---|---|
| Token support/mass carriers | `InfoGeometry.PositiveMeasure`, `InfoGeometry.Canonical.PositiveRayCore` | `count` | Raw occupancy/support and positive mass representatives | Input substrate for routing and attention weights |
| Normalized relational weights | `InfoGeometry.LLM.ThermodynamicSwitching`, `InfoGeometry.LLM.ScalarThermoBridge` | `projective` | Gauge-invariant normalization of relational scores | Produces stable attention/router probabilities |
| KMS/softmax thermodynamic identification | `InfoGeometry.LLM.KMSSoftmaxBridge` | `thermo` | Softmax as finite KMS/Gibbs weighting | Converts scores into thermal selection law |
| Attention + residual recomposition cell | `InfoGeometry.LLM.TransformerBlock`, `InfoGeometry.LLM.TransformerArchitecture.DecoderLayer` | `operator` | Operatorial coupling and additive recomposition | Canonical update cell |
| Split channels and conjugate structure | `InfoGeometry.LLM.SpectralToken`, `InfoGeometry.LLM.PinCPTBridge` | `krein` | Dual/split channel structure, odd/even symmetry action | Signed/chiral lane semantics |
| Transport-constrained layer evolution | `InfoGeometry.LLM.SpinPinTransformerLayer`, `InfoGeometry.LLM.Llama4SpinSpec` | `transport` | Equivariance and constrained propagation through flow | Time/context transport consistency |
| Mask restriction law | `InfoGeometry.LLM.MaskedTransformerBlock`, `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.selectedMask` | `transport` | Admissible channel restriction (global vs local mask) | Causal/context gating |
| Sparse routed expert sector | `InfoGeometry.LLM.TrialityMoE`, `InfoGeometry.LLM.Llama4PythonBlockSpec.TopKRouter` | `operator -> thermo` | Sector-selection over expert family | Routed compute path |
| Shared + routed expert composition | `InfoGeometry.LLM.TrialityMoE.SharedRoutedMoEBlock`, `InfoGeometry.LLM.Llama4PythonBlockSpec.SharedTopKMoE` | `operator` | Always-on central/shared lane plus routed lane | Stability center + specialization |
| Free-energy and Bayes router updates | `InfoGeometry.LLM.RouterFreeEnergyBridge`, `InfoGeometry.LLM.AllTopThermodynamicRouter`, `InfoGeometry.LLM.DiscreteRouterBayesStep` | `thermo` | Coarse-grained thermodynamic selection | Discrete inference update rule |
| Defect quarantine under mangled prompts | `InfoGeometry.LLM.PromptDefectRegularization`, `InfoGeometry.Canonical.ObserverDefect` | `transport -> thermo` | Non-aligned residual pushed to defect-supported lane | Stability under mixed/perturbed prompts |

## Current Theorem Witnesses

The stack already has direct witnesses for the objective:

- `two_stage_residual_block_update`
- `output_eq_shared_plus_active`
- `run_eq_python_block_update`
- `selectedMask_of_nope`
- `selectedMask_of_local`
- `selectedMask_of_missing_local`
- `softmaxWeight_eq_kmsWeight`
- `routerEntropy_eq_beta_internal_plus_massieu`
- `bayes_router_update_preserves_simplex`
- `defect_quarantined_on_mixed_input`
- `regularizedRun_eq_run_on_mixed_input`
- `run_transport_commute`

## Bridge Obligations (Next)

1. Attention ownership theorem:
   show explicit `projective -> operator` lift law from normalized relational weights to operatorial attention update.
2. Masking ownership theorem:
   show masking is an L4 transport restriction, not an ad hoc decoding primitive.
3. Routing ownership theorem:
   show expert routing is an L5 thermodynamic coarse-graining law with stable free-energy interpretation.
4. Residual recomposition theorem:
   show two-stage residual is the canonical adjacent-level recomposition law.
5. Simulation adequacy theorem:
   show assembled `LLM` stack simulates repo-native information dynamics (not merely neural-network resemblance).

## Anti-Goals

- No theorem names or claims requiring unowned external semantics.
- No “LLM imitation” claims as acceptance criteria.
- No capstone claims without adjacent owner bridges.
