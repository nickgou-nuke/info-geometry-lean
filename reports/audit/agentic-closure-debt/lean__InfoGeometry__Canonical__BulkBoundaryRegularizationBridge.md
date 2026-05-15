# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:46.726020+00:00`
Root: `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **9**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean` | `advisory` | 24 | 0 | 9 | 6 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean`
- module: `InfoGeometry.Canonical.BulkBoundaryRegularizationBridge`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field NontrivialRegularizationPackage.Q_MP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field NontrivialRegularizationPackage.Q_D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field NontrivialRegularizationPackage.rightProjector_ne_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field NontrivialRegularizationPackage.leftProjector_ne_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field NontrivialRegularizationPackage.drazinProjection_ne_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field ZeroModeRegularizationPackage.v_zeroMode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field ZeroModeRegularizationPackage.reg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [advisory] `local-hypothesis-injection` in `theorem moorePenroseRightProjector_ne_one_of_hasZeroMode` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L122 [advisory] `local-hypothesis-injection` in `theorem drazinProjection_ne_one_of_hasZeroMode` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L134 [advisory] `existential-packaging` in `theorem exists_nontrivial_regularization_pair_of_dim_mismatch` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L163 [soft] `classical-witness-smuggling` in `def nontrivialRegularizationPackage_of_dim_mismatch` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L197 [soft] `classical-witness-smuggling` in `def zeroModeRegularizationPackage_of_dim_mismatch` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L223 [advisory] `existential-packaging` in `theorem exists_zeroMode_and_nontrivial_regularization_pair_of_dim_mismatch` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L310 [advisory] `existential-packaging` in `theorem exists_nontrivial_regularization_pair_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

