# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:20.984906+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/RealGWClifford.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **10**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/RealGWClifford.lean` | `advisory` | 23 | 0 | 10 | 3 | 13 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/RealGWClifford.lean`
- module: `InfoGeometry.OperatorAlgebra.RealGWClifford`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `law-field-locker` in `structure-field RealCliffordHilbertModulePacket.cliffordAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field RealCliffordHilbertModulePacket.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field GWOccupationPacket.flipAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L110 [soft] `law-field-locker` in `structure-field GWOccupationPacket.delta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field GWOccupationPacket.complement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [advisory] `existential-packaging` in `def GWRealSplittingTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L202 [soft] `simp-law-injection` in `simp-declaration measureReflectionGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L212 [soft] `simp-law-injection` in `simp-declaration multiplicityComplementGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L223 [soft] `simp-law-injection` in `simp-declaration realStructureInvolutionGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L233 [soft] `simp-law-injection` in `simp-declaration ckRealCompatibilityGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L243 [soft] `simp-law-injection` in `simp-declaration realSplitAutomaticityGuard_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L332 [advisory] `existential-packaging` in `def RealGWToSplitKreinBridgeTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

