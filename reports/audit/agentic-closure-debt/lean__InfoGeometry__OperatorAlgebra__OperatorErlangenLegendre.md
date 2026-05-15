# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:19.752610+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/OperatorErlangenLegendre.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **19**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/OperatorErlangenLegendre.lean` | `advisory` | 48 | 0 | 19 | 10 | 29 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/OperatorErlangenLegendre.lean`
- module: `InfoGeometry.OperatorAlgebra.OperatorErlangenLegendre`
- status: `advisory`
- debt_score: `48`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.correlationList` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.modularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.modularGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.modularDerivation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.modularDerivation_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [advisory] `witness-field-projection` in `structure-field modularDerivation_valid` — witness field `modularDerivation_valid : modularDerivation_law` detected; verify owner-level derivation
  - L84 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.stabilizer` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L88 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.stabilizer_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [advisory] `witness-field-projection` in `structure-field stabilizer_valid` — witness field `stabilizer_valid : stabilizer_law` detected; verify owner-level derivation
  - L96 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.exponentialWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.freeEnergyReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field OperatorErlangenLegendrePacket.exponentialLegendre_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [advisory] `witness-field-projection` in `structure-field exponentialLegendre_valid` — witness field `exponentialLegendre_valid : exponentialLegendre_law` detected; verify owner-level derivation
  - L135 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L170 [soft] `simp-law-injection` in `simp-declaration spectraFirstGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L179 [soft] `simp-law-injection` in `simp-declaration diagonalPrimitiveGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L185 [advisory] `existential-packaging` in `def OperatorErlangenLegendreTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L223 [soft] `law-field-locker` in `structure-field HilbertPolyaOperatorPacket.completedZeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field HilbertPolyaOperatorPacket.IsSpectralValue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [soft] `law-field-locker` in `structure-field HilbertPolyaOperatorPacket.selfAdjointWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [advisory] `witness-field-projection` in `structure-field selfAdjoint_valid` — witness field `selfAdjoint_valid : selfAdjointWitness` detected; verify owner-level derivation
  - L239 [soft] `law-field-locker` in `structure-field HilbertPolyaOperatorPacket.determinantWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L243 [advisory] `witness-field-projection` in `structure-field determinant_valid` — witness field `determinant_valid : determinantWitness` detected; verify owner-level derivation
  - L247 [soft] `law-field-locker` in `structure-field HilbertPolyaOperatorPacket.zero_iff_spectral_value` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L258 [soft] `law-field-locker` in `structure-field HilbertPolyaOperatorPacket.functionalEquationSymmetry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [advisory] `witness-field-projection` in `structure-field functionalEquation_valid` — witness field `functionalEquation_valid : functionalEquationSymmetry` detected; verify owner-level derivation
  - L268 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

