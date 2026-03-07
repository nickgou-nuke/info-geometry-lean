# LLM Triality Synthesis

This note summarizes the canonical bridge from transformer attention to
triality cores and Bott-periodic Clifford structure.

## Chain Overview

1. Triadic core:
   query/key/value routing is modeled as a metric-compatible triadic map.
2. Split `Cl(1,1)` instance:
   the split polarization identity instantiates the geometric attention core.
3. Transformer layering:
   residual, normalization, and masked routing are formalized over the triadic base.
4. Positional dynamics:
   positional encoders act as endomorphic pre-routing dynamics.
5. Bott clock:
   Clifford tower extension implements one-step Bott periodic lift patterns.

## Canonical Route In Code

1. `Canonical/Triality.lean`:
   triadic core, metric compatibility, softmax and multi-head decomposition.
2. `LLM/TransformerBlock.lean` and `LLM/MaskedTransformerBlock.lean`:
   causal transformer scaffolds over geometric attention.
3. `LLM/PositionalEncoding.lean`:
   compositional positional pre-encoding maps.
4. `Canonical/BottPeriodicity.lean`:
   split Clifford one-step periodic isomorphism/tower interfaces.

## Canonical Entry Points

- `InfoGeometry.Canonical.Triality`
- `InfoGeometry.LLM.TransformerBlock`
- `InfoGeometry.LLM.MaskedTransformerBlock`
- `InfoGeometry.LLM.PositionalEncoding`
- `InfoGeometry.Canonical.BottPeriodicity`
