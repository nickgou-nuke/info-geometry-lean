# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:43.466921+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovHomologyFrameEquiv.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **13**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovHomologyFrameEquiv.lean` | `advisory` | 31 | 0 | 13 | 5 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovHomologyFrameEquiv.lean`
- module: `InfoGeometry.Canonical.BogoliubovHomologyFrameEquiv`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [soft] `law-field-locker` in `structure-field HomologyFrameEquiv.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field HomologyFrameEquiv.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field HomologyFrameEquiv.preserves_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field HomologyFrameEquiv.preserves_drazinDefect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field HomologyFrameEquiv.preserves_harmonicProjector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [soft] `law-field-locker` in `structure-field HomologyFrameEquiv.preserves_krein` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field HomologyFrameEquiv.preserves_phaseAxis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L89 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L110 [soft] `skeletal-proof` in `theorem maps_boundary` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `skeletal-proof` in `theorem maps_homologyEquivalent` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `skeletal-proof` in `theorem transportedScalarWitness_readout_eq` — proof appears to close via minimal tactic one-liner
  - L146 [advisory] `local-hypothesis-injection` in `theorem transportedScalarWitness_readout_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [soft] `skeletal-proof` in `theorem maps_drazinDefectState` — proof appears to close via minimal tactic one-liner
  - L180 [soft] `skeletal-proof` in `theorem maps_harmonicProjectorFixed` — proof appears to close via minimal tactic one-liner

