# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:58.123009+00:00`
Root: `lean/InfoGeometry/LLM/TransformerArchitecture.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **39**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/TransformerArchitecture.lean` | `advisory` | 79 | 0 | 39 | 1 | 40 |

## Findings by file

### `lean/InfoGeometry/LLM/TransformerArchitecture.lean`
- module: `InfoGeometry.LLM.TransformerArchitecture`
- status: `advisory`
- debt_score: `79`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L12 [soft] `law-field-locker` in `structure-field RotaryPositionalLayer.rotateQ` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L13 [soft] `law-field-locker` in `structure-field RotaryPositionalLayer.rotateK` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `simp-law-injection` in `simp-declaration rotatePair_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L25 [soft] `simp-law-injection` in `simp-declaration rotatePair_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L36 [soft] `law-field-locker` in `structure-field KramersPairing.partner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `simp-law-injection` in `simp-declaration partner_partner` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `law-field-locker` in `structure-field IropeBlend.mixQ` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field IropeBlend.mixK` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `simp-law-injection` in `simp-declaration query_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration key_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `law-field-locker` in `structure-field BogoliubovTransform.particle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field BogoliubovTransform.hole` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `simp-law-injection` in `simp-declaration forwardPair_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [soft] `simp-law-injection` in `simp-declaration forwardPair_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L106 [soft] `law-field-locker` in `structure-field KVCache.keyAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field KVCache.valueAt` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [soft] `simp-law-injection` in `simp-declaration keyAt_write_same` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration valueAt_write_same` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `simp-law-injection` in `simp-declaration keyAt_write_ne` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `simp-law-injection` in `simp-declaration valueAt_write_ne` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `law-field-locker` in `structure-field GatedFeedForward.gateProj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L147 [soft] `law-field-locker` in `structure-field GatedFeedForward.upProj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L148 [soft] `law-field-locker` in `structure-field GatedFeedForward.activate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L149 [soft] `law-field-locker` in `structure-field GatedFeedForward.combine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field GatedFeedForward.downProj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [soft] `simp-law-injection` in `simp-declaration run_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L173 [soft] `law-field-locker` in `structure-field DecoderLayer.preAttentionNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field DecoderLayer.attention` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field DecoderLayer.preFFNNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [soft] `law-field-locker` in `structure-field DecoderLayer.feedForward` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L199 [soft] `skeletal-proof` in `theorem run_eq_two_stage_residual` — proof appears to close via minimal tactic one-liner
  - L214 [soft] `simp-law-injection` in `simp-declaration runDecoderStack_nil` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L218 [soft] `simp-law-injection` in `simp-declaration runDecoderStack_cons` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L237 [soft] `law-field-locker` in `structure-field TransformerBackbone.tokenEmbedding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `law-field-locker` in `structure-field TransformerBackbone.finalNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [soft] `simp-law-injection` in `simp-declaration hiddenState_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L253 [soft] `simp-law-injection` in `simp-declaration normalizedState_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L262 [soft] `law-field-locker` in `structure-field DecoderLanguageModel.lmHead` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L270 [soft] `simp-law-injection` in `simp-declaration logits_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

