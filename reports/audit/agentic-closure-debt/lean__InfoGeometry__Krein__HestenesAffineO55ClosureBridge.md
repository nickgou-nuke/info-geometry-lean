# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:51.284619+00:00`
Root: `lean/InfoGeometry/Krein/HestenesAffineO55ClosureBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **10**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HestenesAffineO55ClosureBridge.lean` | `advisory` | 28 | 0 | 10 | 8 | 18 |

## Findings by file

### `lean/InfoGeometry/Krein/HestenesAffineO55ClosureBridge.lean`
- module: `InfoGeometry.Krein.HestenesAffineO55ClosureBridge`
- status: `advisory`
- debt_score: `28`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L71 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.duality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.o55VectorAction_krein_isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.o55_volumeState_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.o55_maps_hurwitzRoots` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.cl55_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.affine_extension_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.o55_isometry_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L125 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.affine_closure_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [soft] `law-field-locker` in `structure-field HestenesAffineO55ClosureBridge.affine_closure_iff_o55` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L136 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L136 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L151 [advisory] `bridge-shaped-declaration` in `theorem cl55_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L157 [advisory] `bridge-shaped-declaration` in `theorem affine_extension_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L163 [advisory] `bridge-shaped-declaration` in `theorem o55_isometry_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L169 [advisory] `bridge-shaped-declaration` in `theorem affine_closure_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

