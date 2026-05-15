# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:48.280685+00:00`
Root: `lean/InfoGeometry/Canonical/RealHestenesKreinHomology.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **14**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealHestenesKreinHomology.lean` | `advisory` | 37 | 0 | 14 | 9 | 23 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealHestenesKreinHomology.lean`
- module: `InfoGeometry.Canonical.RealHestenesKreinHomology`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field RealDifferential.D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field RealDifferential.D_sq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L63 [advisory] `existential-packaging` in `def IsBoundary` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L81 [advisory] `existential-packaging` in `def HomologyEquivalent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [soft] `skeletal-proof` in `theorem HomologyEquivalent_symm` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `skeletal-proof` in `theorem HomologyEquivalent_trans` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `law-field-locker` in `structure-field BoundaryVanishingWitness.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [soft] `law-field-locker` in `structure-field BoundaryVanishingWitness.vanishes_on_boundaries` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L148 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L157 [advisory] `local-hypothesis-injection` in `theorem descends_to_homology_equivalence` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L182 [soft] `law-field-locker` in `structure-field DrazinNullSupport.IsDrazinNull` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L184 [soft] `law-field-locker` in `structure-field DrazinNullSupport.IsGeneralizedKernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field DrazinNullSupport.null_iff_generalizedKernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L220 [soft] `skeletal-proof` in `theorem isDrazinNullCycle_iff_mem_drazinCore` — proof appears to close via minimal tactic one-liner
  - L283 [soft] `law-field-locker` in `structure-field NullProjector.P0_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L289 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L348 [soft] `law-field-locker` in `structure-field HestenesKreinDoubledFrame.U` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L349 [soft] `law-field-locker` in `structure-field HestenesKreinDoubledFrame.kreinPreserving` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L351 [soft] `law-field-locker` in `structure-field HestenesKreinDoubledFrame.phasePreserving` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L358 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

