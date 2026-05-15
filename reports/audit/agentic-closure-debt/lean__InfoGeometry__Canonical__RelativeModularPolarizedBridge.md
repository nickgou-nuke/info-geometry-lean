# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:51.225066+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **17**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean` | `advisory` | 39 | 0 | 17 | 5 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularPolarizedBridge.lean`
- module: `InfoGeometry.Canonical.RelativeModularPolarizedBridge`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `existential-packaging` in `structure PlusRestrictedRelativeModularData` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L42 [soft] `law-field-locker` in `structure-field PlusRestrictedRelativeModularData.lift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field PlusRestrictedRelativeModularData.lift_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L44 [advisory] `existential-packaging` in `structure MinusRestrictedRelativeModularData` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L50 [soft] `law-field-locker` in `structure-field MinusRestrictedRelativeModularData.lift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field MinusRestrictedRelativeModularData.lift_mem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [advisory] `existential-packaging` in `structure PolarizedRelativeModularPair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L60 [soft] `law-field-locker` in `structure-field PolarizedRelativeModularPair.sameCarrier` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [advisory] `existential-packaging` in `theorem MinusRestrictedRelativeModularData.lift_eq_minusPoint_snd` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L71 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L89 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_pullback_ambient_add_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L193 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L216 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.local_projectiveLogGenerator_eq_projectiveCountHamiltonianProfile_of_countRays` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

