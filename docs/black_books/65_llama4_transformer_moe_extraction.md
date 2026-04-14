# 65. Llama 4 Transformer/MoE Extraction for Formalization

*Date: April 14, 2026*
*Context: Operator-first formalization intake from official Meta Python source*

## Source Snapshot

Primary extracted files (official `meta-llama/llama-models`):

- `external_refs/llama4/model.py`
- `external_refs/llama4/moe.py`
- `external_refs/llama4/ffn.py`
- `external_refs/llama4/args.py`
- `external_refs/llama4/datatypes.py`

## Exact Block to Formalize

From `model.py`, `TransformerBlock.forward`:

- Line pattern in source:
  - residual-attention step: `h = x + attention(attention_norm(x), ...)`
  - residual-ffn step: `out = h + feed_forward(ffn_norm(h))`

In local snapshot:

- `external_refs/llama4/model.py` lines 332-334

This is the canonical two-residual update law:

$$
\begin{aligned}
h_l &= x_l + \operatorname{Attn}(\operatorname{Norm}_a(x_l)), \\
x_{l+1} &= h_l + \operatorname{FFN}(\operatorname{Norm}_f(h_l)).
\end{aligned}
$$

## MoE Routing Semantics to Formalize

From `moe.py`, `MoE.forward`:

- Router logits: matmul input with router matrix.
- Sparse gate: `topk` keeps only top-K entries, others are set to `-inf` before sigmoid.
- Routed input: gathered per-route token lanes and weighted by gated scores.
- Output merge: `shared_expert(x)` + scatter-add of routed expert outputs.

In local snapshot:

- `external_refs/llama4/moe.py` lines 181-210

Formalization-safe split:

$$
\mathrm{MoE}(x)=\mathrm{Shared}(x)+\mathrm{Routed}_{\text{active}}(x),
$$

with inactive routes represented as defect-gated mass (zeroed weights).

## Repo-Native Mapping (Current Lean)

Already aligned with:

- `lean/InfoGeometry/LLM/TrialityMoE.lean`
  - `SparseRouter.router_weight_split`
  - `TrialityMoEBlock.moe_output_split`
  - `RouterDefectBridge.sourcedGenerator_eq_canonical`
  - `RouterDefectBridge.sourcedGenerator_respects_cut`

## Why code-first extraction helps formalization

Yes: extracting directly from vendor code reduces theorem drift.

- It gives explicit update equations to preserve.
- It disambiguates router behavior (`topk` + hard-zero inactive path).
- It allows staged Lean formalization: algebraic split first, semantics bridge second.

## Next Formal Targets

1. Add a Lean theorem surface for two-stage residual block law (attention then ffn).
2. Add a gate law mirroring `topk` hard sparsity as a `gate` predicate axiom package.
3. Add a shared-plus-routed decomposition theorem mirroring `out_aD = shared + scatter_add(routed)`.
4. Keep interpretation (triality/physics language) in docs, not in theorem premises.
