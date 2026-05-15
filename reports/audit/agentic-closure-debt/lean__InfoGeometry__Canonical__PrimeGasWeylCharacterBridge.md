# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:44.140950+00:00`
Root: `lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **6**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/PrimeGasWeylCharacterBridge.lean`
- module: `InfoGeometry.Canonical.PrimeGasWeylCharacterBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `law-field-locker` in `structure-field PrimeGasWeylCharacterBridge.beta_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field PrimeGasWeylCharacterBridge.entropy_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field PrimeGasWeylCharacterBridge.weylCharacter_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L60 [soft] `simp-law-injection` in `simp-declaration souriau_beta_eq_primeGas_beta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `simp-law-injection` in `simp-declaration souriau_entropy_eq_primeGas_entropy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration weylCharacter_eq_primeGas_character` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

