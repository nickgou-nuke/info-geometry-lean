# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:55.381969+00:00`
Root: `lean/InfoGeometry/LLM/AllTopThermodynamicTransformer.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **12**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/AllTopThermodynamicTransformer.lean` | `advisory` | 36 | 0 | 12 | 12 | 24 |

## Findings by file

### `lean/InfoGeometry/LLM/AllTopThermodynamicTransformer.lean`
- module: `InfoGeometry.LLM.AllTopThermodynamicTransformer`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L12 [advisory] `existential-packaging` in `structure ReusedAllTopLayer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L40 [advisory] `existential-packaging` in `def runState` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L50 [soft] `simp-law-injection` in `simp-declaration runToken_eq_base_plus_routed` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `skeletal-proof` in `theorem runToken_eq_base_plus_routed` — proof appears to close via minimal tactic one-liner
  - L67 [advisory] `existential-packaging` in `theorem runToken_eq_base_plus_normalizedMixture` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L85 [advisory] `existential-packaging` in `def runLayerStack` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [soft] `simp-law-injection` in `simp-declaration runLayerStack_nil` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `simp-law-injection` in `simp-declaration runLayerStack_cons` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [advisory] `existential-packaging` in `def runDecoderStackPointwise` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L129 [advisory] `existential-packaging` in `def zeroMoE` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L137 [soft] `simp-law-injection` in `simp-declaration allTopMixture_zeroMoE` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [advisory] `existential-packaging` in `def withZeroMoE` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L164 [advisory] `existential-packaging` in `theorem runState_withZeroMoE_eq_pointwise` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L184 [advisory] `existential-packaging` in `theorem runLayerStack_map_withZeroMoE_eq_pointwise` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L216 [soft] `law-field-locker` in `structure-field AllTopThermodynamicBackbone.tokenEmbedding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field AllTopThermodynamicBackbone.finalNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L236 [soft] `law-field-locker` in `structure-field AllTopThermodynamicLanguageModel.backbone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L237 [soft] `law-field-locker` in `structure-field AllTopThermodynamicLanguageModel.lmHead` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [advisory] `existential-packaging` in `def liftBaseWithRoute` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L270 [soft] `simp-law-injection` in `simp-declaration liftBaseWithRoute_tokenEmbedding` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L276 [soft] `simp-law-injection` in `simp-declaration liftBaseWithRoute_finalNorm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L282 [soft] `simp-law-injection` in `simp-declaration liftBaseWithRoute_lmHead` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L290 [advisory] `existential-packaging` in `def liftBaseWithZeroMoE` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

