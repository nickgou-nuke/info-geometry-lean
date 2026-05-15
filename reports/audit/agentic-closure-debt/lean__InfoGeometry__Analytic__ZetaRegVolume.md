# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:30.205672+00:00`
Root: `lean/InfoGeometry/Analytic/ZetaRegVolume.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **13**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Analytic/ZetaRegVolume.lean` | `advisory` | 27 | 0 | 13 | 1 | 14 |

## Findings by file

### `lean/InfoGeometry/Analytic/ZetaRegVolume.lean`
- module: `InfoGeometry.Analytic.ZetaRegVolume`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [soft] `law-field-locker` in `structure-field HeatKernelWitness.supertrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L20 [soft] `law-field-locker` in `structure-field HeatKernelWitness.traceClass` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L21 [soft] `law-field-locker` in `structure-field HeatKernelWitness.smallTimeAsymptotics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `law-field-locker` in `structure-field HeatKernelWitness.mellinBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field SpectralZetaWitness.spectralZeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field SpectralZetaWitness.analyticContinuation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field EmergentVolumeWitness.volumeMatches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field SplitZetaSupervolumeShadow.operator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field SplitZetaSupervolumeShadow.supertraceReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field SplitZetaSupervolumeShadow.superBerezinianReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field SplitZetaSupervolumeShadow.zetaLikePotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `simp-law-injection` in `simp-declaration zetaLikePotential_eq_neg_log_superBerezinian` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `skeletal-proof` in `theorem zetaLikePotential_eq_neg_log_superBerezinian` — proof appears to close via minimal tactic one-liner

