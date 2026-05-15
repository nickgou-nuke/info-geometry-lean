# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:14.467639+00:00`
Root: `lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **5**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean` | `advisory` | 15 | 0 | 5 | 5 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean`
- module: `InfoGeometry.Canonical.YangMillsFiniteBridge`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L52 [advisory] `local-hypothesis-injection` in `theorem spectralGapFromLogDet_pos_of_coercive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L61 [soft] `law-field-locker` in `structure-field FiniteYangMillsBridge.n_ge_two` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field FiniteYangMillsBridge.hJointKernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field FiniteYangMillsBridge.hCommOrthogonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field FiniteYangMillsBridge.spectral_gap_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field FiniteYangMillsBridge.gamma_le_spectral_gap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [advisory] `bridge-shaped-declaration` in `theorem existenceClaims_of_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L154 [advisory] `existential-packaging` in `theorem existenceClaims_of_bridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L170 [advisory] `bridge-shaped-declaration` in `theorem obligations_of_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

