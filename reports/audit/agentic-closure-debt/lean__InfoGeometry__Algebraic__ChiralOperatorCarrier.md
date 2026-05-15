# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:27.796061+00:00`
Root: `lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **21**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean` | `advisory` | 43 | 0 | 21 | 1 | 22 |

## Findings by file

### `lean/InfoGeometry/Algebraic/ChiralOperatorCarrier.lean`
- module: `InfoGeometry.Algebraic.ChiralOperatorCarrier`
- status: `advisory`
- debt_score: `43`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.boost` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.uPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.uMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.conformalOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.boost_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.boost_eps_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.eps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.uPlus_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.uMinus_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.uPlus_add_uMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.uPlus_comp_uMinus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.uMinus_comp_uPlus` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.conformal_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field ChiralOperatorCarrier.conformal_sq_neg_id` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `simp-law-injection` in `simp-declaration canonicalChiralOperatorCarrier_boost_eq_modular_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration canonicalChiralOperatorCarrier_eps_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration canonicalChiralOperatorCarrier_uPlus_eq_Pplus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration canonicalChiralOperatorCarrier_uMinus_eq_Pminus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration canonicalChiralOperatorCarrier_conformalOperator_eq_K` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `skeletal-proof` in `theorem canonicalChiralOperatorCarrier_eps_eq_uPlus_sub_uMinus` — proof appears to close via minimal tactic one-liner

