# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:34.934315+00:00`
Root: `lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **23**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean` | `advisory` | 47 | 0 | 23 | 1 | 24 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/ZetaTraceVielbeinSpecialization.lean`
- module: `InfoGeometry.Arithmetic.ZetaTraceVielbeinSpecialization`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [soft] `simp-law-injection` in `simp-declaration primeLocalJacobian_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L55 [soft] `skeletal-proof` in `theorem primeLocalJacobian_def` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `simp-law-injection` in `simp-declaration primeLocalVolumeFactor_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `skeletal-proof` in `theorem primeLocalVolumeFactor_def` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `simp-law-injection` in `simp-declaration primeLocalEffectiveAction_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `skeletal-proof` in `theorem primeLocalEffectiveAction_def` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `skeletal-proof` in `theorem zetaTraceEulerSupervolume_eq_riemannZeta` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `skeletal-proof` in `theorem zetaTraceSupervolume_eq_riemannZeta` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `law-field-locker` in `structure-field PrimeVielbeinCarrier.convergenceDomain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field PrimeVielbeinCarrier.localJacobian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field PrimeVielbeinCarrier.localVolumeFactor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field PrimeVielbeinCarrier.localEffectiveAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field PrimeVielbeinCarrier.effectiveAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L110 [soft] `law-field-locker` in `structure-field PrimeVielbeinCarrier.traceLogSupervolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [soft] `law-field-locker` in `structure-field PrimeVielbeinCarrier.eulerSupervolume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `simp-law-injection` in `simp-declaration canonicalPrimeVielbein_convergenceDomain` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L128 [soft] `simp-law-injection` in `simp-declaration canonicalPrimeVielbein_traceLogSupervolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `skeletal-proof` in `theorem canonicalPrimeVielbein_traceLogSupervolume` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `simp-law-injection` in `simp-declaration canonicalPrimeVielbein_eulerSupervolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L136 [soft] `skeletal-proof` in `theorem canonicalPrimeVielbein_eulerSupervolume` — proof appears to close via minimal tactic one-liner
  - L140 [soft] `skeletal-proof` in `theorem canonicalPrimeVielbein_traceLogSupervolume_eq_riemannZeta` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `skeletal-proof` in `theorem canonicalPrimeVielbein_eulerSupervolume_eq_riemannZeta` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `skeletal-proof` in `theorem canonicalPrimeVielbein_traceLog_eq_eulerSupervolume` — proof appears to close via minimal tactic one-liner

