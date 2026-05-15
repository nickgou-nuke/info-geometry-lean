# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:11.336896+00:00`
Root: `lean/InfoGeometry/Canonical/WeylCharacterVandermondeShadow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **4**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylCharacterVandermondeShadow.lean` | `advisory` | 14 | 0 | 4 | 6 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylCharacterVandermondeShadow.lean`
- module: `InfoGeometry.Canonical.WeylCharacterVandermondeShadow`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L58 [soft] `skeletal-proof` in `theorem value_eq_determinant` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `law-field-locker` in `structure-field D4CharacterVandermondePacket.denominatorNodes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field D4CharacterVandermondePacket.numerator_eq_vector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L84 [soft] `law-field-locker` in `structure-field D4CharacterVandermondePacket.denominatorWitness_nodes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L102 [advisory] `existential-packaging` in `theorem denominator_eq_zero_iff_collision` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L122 [advisory] `bridge-shaped-declaration` in `theorem finite_character_denominator_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L122 [advisory] `existential-packaging` in `theorem finite_character_denominator_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

