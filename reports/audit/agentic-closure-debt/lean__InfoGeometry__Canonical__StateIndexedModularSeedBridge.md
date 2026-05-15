# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:02.339894+00:00`
Root: `lean/InfoGeometry/Canonical/StateIndexedModularSeedBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **5**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/StateIndexedModularSeedBridge.lean` | `advisory` | 14 | 0 | 5 | 4 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/StateIndexedModularSeedBridge.lean`
- module: `InfoGeometry.Canonical.StateIndexedModularSeedBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L53 [soft] `law-field-locker` in `structure-field StateIndexedSeedDatum.kms` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `skeletal-proof` in `theorem modularTransportGenerator_stateIndexedBivectorSeed` — proof appears to close via minimal tactic one-liner
  - L87 [advisory] `local-hypothesis-injection` in `theorem modularTransportGenerator_stateIndexedBivectorSeed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L108 [soft] `law-field-locker` in `structure-field BoundedCanonicalSeedWitness.datum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field BoundedCanonicalSeedWitness.hInverseTemperature_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [soft] `skeletal-proof` in `theorem stateIndexedBoostGenerator_eq_superHamiltonian_of_boundedWitness` — proof appears to close via minimal tactic one-liner

