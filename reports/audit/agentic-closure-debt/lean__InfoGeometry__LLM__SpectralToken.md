# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:57.767761+00:00`
Root: `lean/InfoGeometry/LLM/SpectralToken.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **19**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/SpectralToken.lean` | `advisory` | 39 | 0 | 19 | 1 | 20 |

## Findings by file

### `lean/InfoGeometry/LLM/SpectralToken.lean`
- module: `InfoGeometry.LLM.SpectralToken`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `simp-law-injection` in `simp-declaration swap_primal` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L23 [soft] `simp-law-injection` in `simp-declaration swap_dual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L26 [soft] `simp-law-injection` in `simp-declaration swap_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `law-field-locker` in `structure-field TokenEncoder.encode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `simp-law-injection` in `simp-declaration primalMap_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration dualMap_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `law-field-locker` in `structure-field SpectralGrading.grade` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field SpectralGrading.involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `simp-law-injection` in `simp-declaration actToken_primal` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration actToken_dual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration actToken_involutive` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `law-field-locker` in `structure-field QKVTrialityCarrier.pair` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `simp-law-injection` in `simp-declaration evaluate_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L110 [soft] `law-field-locker` in `structure-field KramersQKBridge.toKey` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [soft] `law-field-locker` in `structure-field KramersQKBridge.toQuery` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [soft] `law-field-locker` in `structure-field KramersQKBridge.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field KramersQKBridge.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `simp-law-injection` in `simp-declaration toQuery_toKey` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L122 [soft] `simp-law-injection` in `simp-declaration toKey_toQuery` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

