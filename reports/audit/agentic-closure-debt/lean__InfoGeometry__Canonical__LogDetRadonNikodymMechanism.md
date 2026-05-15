# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:26.144046+00:00`
Root: `lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **6**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean` | `advisory` | 15 | 0 | 6 | 3 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean`
- module: `InfoGeometry.Canonical.LogDetRadonNikodymMechanism`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L71 [soft] `law-field-locker` in `structure-field TypeIIILogDetRNPackage.cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field TypeIIILogDetRNPackage.scalarBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `skeletal-proof` in `theorem logPotential_add` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem cocycle_chain_rule` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `simp-law-injection` in `simp-declaration logPotential_eq_boltzmannEntropyPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [advisory] `existential-packaging` in `theorem exists_additive_logPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L102 [advisory] `existential-packaging` in `theorem exists_boltzmannEntropyPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L102 [soft] `skeletal-proof` in `theorem exists_boltzmannEntropyPotential` — proof appears to close via minimal tactic one-liner

