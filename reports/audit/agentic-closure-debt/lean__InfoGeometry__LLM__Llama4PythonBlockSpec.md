# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:56.583103+00:00`
Root: `lean/InfoGeometry/LLM/Llama4PythonBlockSpec.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **24**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/Llama4PythonBlockSpec.lean` | `advisory` | 49 | 0 | 24 | 1 | 25 |

## Findings by file

### `lean/InfoGeometry/LLM/Llama4PythonBlockSpec.lean`
- module: `InfoGeometry.LLM.Llama4PythonBlockSpec`
- status: `advisory`
- debt_score: `49`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `law-field-locker` in `structure-field TopKRouter.rawScore` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field TopKRouter.selected` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field TopKRouter.selected_card_le` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `simp-law-injection` in `simp-declaration weight_of_selected` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L40 [soft] `skeletal-proof` in `theorem weight_of_selected` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `simp-law-injection` in `simp-declaration weight_of_not_selected` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `skeletal-proof` in `theorem weight_of_not_selected` — proof appears to close via minimal tactic one-liner
  - L78 [soft] `law-field-locker` in `structure-field SharedTopKMoE.sharedExpert` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [soft] `law-field-locker` in `structure-field SharedTopKMoE.routedExpert` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field SharedTopKMoE.router` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `simp-law-injection` in `simp-declaration output_eq_shared_plus_total` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `skeletal-proof` in `theorem output_eq_shared_plus_total` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `law-field-locker` in `structure-field TransformerBlock.attentionNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field TransformerBlock.ffnNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field TransformerBlock.attention` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field TransformerBlock.feedForward` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L153 [soft] `law-field-locker` in `structure-field TransformerBlock.useRope_eq_not_isNope` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field TransformerBlock.useQkNorm_eq_base_and_not_isNope` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `simp-law-injection` in `simp-declaration selectedMask_of_nope` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L170 [soft] `simp-law-injection` in `simp-declaration selectedMask_of_local` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L178 [soft] `simp-law-injection` in `simp-declaration selectedMask_of_missing_local` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L185 [soft] `simp-law-injection` in `simp-declaration useRope_eq_not_nope` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L189 [soft] `simp-law-injection` in `simp-declaration useQkNorm_eq_base_and_not_nope` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L206 [soft] `skeletal-proof` in `theorem run_eq_python_block_update` — proof appears to close via minimal tactic one-liner

