# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:50.739166+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **10**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularCore.lean` | `advisory` | 24 | 0 | 10 | 4 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularCore.lean`
- module: `InfoGeometry.Canonical.RelativeModularCore`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `existential-packaging` in `structure RelativeStatePair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L52 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.modularPotential_eq_neg_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.modularPotential_eq_logDensity_target_sub_source` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [advisory] `existential-packaging` in `def RelativeStatePair.compose` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L72 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.compose_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.compose_modularPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [advisory] `existential-packaging` in `structure RestrictedRelativeModularData` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L117 [soft] `law-field-locker` in `structure-field RestrictedRelativeModularData.source_logDensity_eq_pullback_add_shift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field RestrictedRelativeModularData.target_logDensity_eq_pullback_add_shift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.local_logDensity_eq_pullback_add_shiftDiff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L158 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.local_modularPotential_eq_pullback_add_shiftDiff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L173 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.local_logDensity_eq_pullback_of_equal_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L183 [soft] `simp-law-injection` in `simp-declaration RestrictedRelativeModularData.local_modularPotential_eq_pullback_of_equal_shift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

