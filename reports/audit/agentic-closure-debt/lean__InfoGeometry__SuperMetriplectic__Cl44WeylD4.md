# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:42.094367+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/Cl44WeylD4.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **16**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/Cl44WeylD4.lean` | `advisory` | 33 | 0 | 16 | 1 | 17 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/Cl44WeylD4.lean`
- module: `InfoGeometry.SuperMetriplectic.Cl44WeylD4`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `simp-law-injection` in `simp-declaration value_plus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `simp-law-injection` in `simp-declaration value_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `theorem coordinate_i` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `theorem coordinate_j` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `law-field-locker` in `structure-field D4SpinorWeight.signs` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field D4SpinorWeight.positiveChirality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field D4SpinorWeight.chiralityProof` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field Cl44D4CartanCharacterSkeleton.cartanTemperature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field Cl44D4CartanCharacterSkeleton.stressProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field Cl44D4CartanCharacterSkeleton.centralChargeProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field Cl44D4CartanCharacterSkeleton.totalProjection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field Cl44D4CartanCharacterSkeleton.totalProjection_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `skeletal-proof` in `theorem cartan_rank_four` — proof appears to close via minimal tactic one-liner
  - L166 [soft] `law-field-locker` in `structure-field Cl44BPSDominantCharacterPacket.isDominantBPSWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [soft] `law-field-locker` in `structure-field Cl44BPSDominantCharacterPacket.centralProjection_saturates` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L171 [soft] `law-field-locker` in `structure-field Cl44BPSDominantCharacterPacket.stressProjection_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

