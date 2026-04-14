# 70. Hypothesis Registry (Common Unconscious Stream)

*Date: April 15, 2026*  
*Scope: Preserve speculative pearls without pruning; map testable parts to formal surfaces.*

## Status Legend

- `SPEC`: speculative/metaphoric, not formalized yet
- `UNPROVEN`: mathematically stated but not yet closed in Lean owner surfaces
- `TESTABLE`: has a direct formal hook in current Lean surfaces

## Evidence Tier Legend

- `EXTERNAL_FACT`: established in external literature; not canon unless translated to owner surfaces
- `REPO_THEOREM`: closed Lean theorem on owner surfaces
- `ANALOGY`: structured mapping language, not a theorem identity
- `SPECULATIVE`: conjectural bridge or metaphoric claim

## Registry

| ID | Status | Evidence Tier | Hypothesis | Verbatim Trigger Quote | Lean Hook (if any) |
|---|---|---|---|---|---|
| H70-001 | TESTABLE | ANALOGY | RoPE lane behaves as compact phase axis (shape-preserving orientation lane). | "RoPE ... compact K-axis ... pure shape with no scale." | `InfoGeometry.LLM.Llama4PythonBlockSpec.TransformerBlock.useRope_eq_not_nope` |
| H70-002 | SPEC | ANALOGY | HyperRoPE/HoPE corresponds to hyperbolic boost axis and long-context monotone decay geometry. | "HyperRoPE / HoPE ... Hyperbolic Boost Axis (A)." | `InfoGeometry.LLM.SpinPinTransformerLayer` (conceptual anchor only) |
| H70-003 | TESTABLE | REPO_THEOREM | Router thermodynamic lane is governed by free-energy/Massieu identity. | "scaled dot-product attention ... Weyl Gauge ... thermal KMS state" | `InfoGeometry.LLM.RouterFreeEnergyBridge.beta_mul_routerFreeEnergy_eq_neg_routerMassieu` |
| H70-004 | TESTABLE | REPO_THEOREM | Per-layer scale/shape split is preserved in all-top routed engine. | "decompose latent space into scale and shape" | `InfoGeometry.LLM.TransformerPhysicsEngine.scale_shape_split_preserved_per_layer` |
| H70-005 | TESTABLE | REPO_THEOREM | Defect quarantine survives stack composition under zero-routed branch map. | "quarantine ... defect ... boundary" | `InfoGeometry.LLM.TransformerPhysicsEngine.defect_quarantine_preserved_under_stack` |
| H70-006 | SPEC | SPECULATIVE | Residual stream acts as Jaynes reference-state measurement frame. | "Residual Stream: The Jaynes Reference State" | pending dedicated module |
| H70-007 | TESTABLE | REPO_THEOREM | Krein/split-signature interaction is available as an explicit attention-energy surface. | "Euclidean illusion vs Krein reality" | `InfoGeometry.LLM.KreinAttentionEnergy.kreinInteractionEnergy_eq_neg_splitB11` |
| H70-008 | TESTABLE | REPO_THEOREM | Softmax/KMS weighting is finite-normalized on each token-local expert slice. | "Softmax as the Unruh Thermal Bath (KMS State)" | `InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_sum_one` |
| H70-009 | SPEC | ANALOGY | iRoPE/nope interleaving behaves as dynamic gauge field queried only on defects. | "position becomes a dynamic gauge field" | pending explicit theorem surface |
| H70-010 | SPEC | SPECULATIVE | Horizon inversion gate `Q -> -Q` cancels local thermal fluctuation. | "horizon acts as an inversion mirror (Q -> -Q)" | pending |
| H70-011 | SPEC | SPECULATIVE | Majorana-like paired latent modes yield topological fault tolerance. | "Majorana Zero Modes in the Latent Space" | pending |
| H70-012 | UNPROVEN | SPECULATIVE | Transformer as discrete Tomita-Takesaki flow engine. | "Transformer is a discrete Tomita-Takesaki flow engine." | pending |

## Immediate Formalization Queue (One-Week Target)

1. Lock Rosetta calibration in chapter `71` and require evidence-tier tag on each new H70 claim.
2. Decide if `H70-010` stays metaphorical (`SPEC`) or graduates to a formal involutive transport interface.
3. Add a joint `KMS + logit + partition` capstone package theorem for the `H70-008` lane.
4. Keep Chapter 70 test hooks strictly on info-geometric/thermodynamic owners (KMS, Massieu, KL/Bregman), not Euclidean comparison baselines.

## Policy for This Chapter

- Repeats are preserved.
- Improbable hypotheses are not pruned.
- Speculation is retained and tagged instead of normalized away.
