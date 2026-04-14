# 71. Rosetta Calibration for AQFT ↔ Transformer Claims

*Date: April 15, 2026*  
*Purpose: enforce a hard split between proved facts, Lean-closed surfaces, analogies, and speculative bridges.*

## Authority Bands

- `PROVED_EXTERNAL`: established in external math/physics or model-spec literature.
- `REPO_THEOREM`: closed Lean theorem on owner surfaces in this repo.
- `OPERATOR_ANALOGY`: structured mapping language; useful but not identity-level proof.
- `SPECULATIVE_BRIDGE`: conjectural extension not yet theorem-safe.

## Rosetta Matrix

| AQFT / Operator Object | Transformer Object | Repo Owner Surface | Authority Band | Notes |
|---|---|---|---|---|
| Wedge modular flow (Bisognano–Wichmann lane) | Causal context restriction and directed propagation | `InfoGeometry.LLM.MaskedTransformerBlock` | `OPERATOR_ANALOGY` | keep as analogy until explicit modular-flow theorem family exists |
| KMS thermodynamic normalization | Softmax/Gibbs normalized weights | `InfoGeometry.LLM.KMSSoftmaxBridge` | `REPO_THEOREM` | finite-token KMS bridge is already closed |
| Compact phase rotation | RoPE positional rotation lane | `InfoGeometry.LLM.Llama4PythonBlockSpec` | `OPERATOR_ANALOGY` | architecture-level mapping; not AQFT identity |
| Non-compact boost lane | Hyperbolic positional/boost heuristics (HoPE-like) | `InfoGeometry.LLM.SpinPinTransformerLayer` | `OPERATOR_ANALOGY` | usable design language, currently not promoted to theorem identity |
| Scale control under repeated flow | RMSNorm/normalization stabilizer | `InfoGeometry.LLM.TransformerPhysicsEngine` | `OPERATOR_ANALOGY` | use as scale/shape interpretation only |
| Defect sink / quarantine | routed-vs-defect split under perturbation | `InfoGeometry.LLM.PromptDefectRegularization` | `REPO_THEOREM` | formal defect quarantine lane present |
| Exact modular-Rindler integrator claim | full transformer as AQFT modular engine | `H70-012` (`HypothesisScaffold70`) | `SPECULATIVE_BRIDGE` | not promotable yet |

## Promotion Rules

1. `OPERATOR_ANALOGY` claims cannot be narrated as equalities; they require a new owner theorem family before promotion.
2. `SPECULATIVE_BRIDGE` claims must stay tagged as speculative in black-book and registry surfaces.
3. `PROVED_EXTERNAL` facts are never canonical by themselves; they must be translated into owner symbols and compiled.
4. `REPO_THEOREM` is the only band allowed for capstone dependency chains.

## Immediate Build Targets

1. Extend `H70-013` to context-level weight-comparison constraints.
2. Add an involutive transport interface candidate for `H70-010` without promoting beyond speculative.
3. Keep `H70-012` as conjectural until a modular-flow theorem skeleton is owner-complete.
