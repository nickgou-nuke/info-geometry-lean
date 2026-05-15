# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:58.244686+00:00`
Root: `lean/InfoGeometry/LLM/TransformerBlock.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **10**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/TransformerBlock.lean` | `advisory` | 22 | 0 | 10 | 2 | 12 |

## Findings by file

### `lean/InfoGeometry/LLM/TransformerBlock.lean`
- module: `InfoGeometry.LLM.TransformerBlock`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field TransformerBlock.attn` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field TransformerBlock.residualLift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field TransformerBlock.norm1` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field TransformerBlock.mlp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field TransformerBlock.norm2` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `simp-law-injection` in `simp-declaration attentionOut_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration afterAttention_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration afterMLP_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration run_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `skeletal-proof` in `lemma attentionOut_decomposition_residual` — proof appears to close via minimal tactic one-liner
  - L111 [advisory] `local-hypothesis-injection` in `lemma afterMLP_eq_afterAttention_of_zero_mlp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

