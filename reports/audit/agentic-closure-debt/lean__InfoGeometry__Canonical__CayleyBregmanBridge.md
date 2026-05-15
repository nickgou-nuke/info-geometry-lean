# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:49.348334+00:00`
Root: `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **8**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean` | `advisory` | 24 | 0 | 8 | 8 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/CayleyBregmanBridge.lean`
- module: `InfoGeometry.Canonical.CayleyBregmanBridge`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L13 [soft] `law-field-locker` in `structure-field Transport.toBounded` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L19 [advisory] `bridge-shaped-declaration` in `def Bridge.toBounded` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L22 [advisory] `bridge-shaped-declaration` in `def Bridge.toUnbounded` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L25 [advisory] `bridge-shaped-declaration` in `def Bridge.toTransport` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L29 [soft] `simp-law-injection` in `simp-declaration Bridge.left_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `simp-law-injection` in `simp-declaration Bridge.right_inv` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `law-field-locker` in `structure-field CompatibleDualFlat.D_transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field CompatibleDualFlat.grad_transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [advisory] `local-hypothesis-injection` in `theorem cayley_pythagorean_invariance` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L162 [soft] `skeletal-proof` in `theorem quadraticPotential_deriv` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `skeletal-proof` in `theorem quadraticDualFlat_nabla` — proof appears to close via minimal tactic one-liner
  - L173 [advisory] `local-hypothesis-injection` in `theorem quadraticDualFlat_nabla` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [advisory] `local-hypothesis-injection` in `theorem quadraticDualFlat_nabla` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L180 [advisory] `local-hypothesis-injection` in `theorem quadraticDualFlat_nabla` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L205 [soft] `skeletal-proof` in `theorem cayleyNegationPythagoreanInvariance` — proof appears to close via minimal tactic one-liner

