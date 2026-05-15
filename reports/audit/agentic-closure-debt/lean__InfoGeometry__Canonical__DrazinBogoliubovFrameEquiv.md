# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:01.490333+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinBogoliubovFrameEquiv.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **10**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinBogoliubovFrameEquiv.lean` | `advisory` | 27 | 0 | 10 | 7 | 17 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinBogoliubovFrameEquiv.lean`
- module: `InfoGeometry.Canonical.DrazinBogoliubovFrameEquiv`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L10 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L12 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [soft] `skeletal-proof` in `theorem drazinProjection_add_complementaryProjection` — proof appears to close via minimal tactic one-liner
  - L95 [advisory] `bridge-shaped-declaration` in `theorem drazinProjection_conjugate_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L127 [soft] `law-field-locker` in `structure-field ChiralDrazinKreinPackage.form_preserved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L128 [soft] `law-field-locker` in `structure-field ChiralDrazinKreinPackage.drazin_split_compatible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L129 [soft] `law-field-locker` in `structure-field ChiralDrazinKreinPackage.cl11_laws` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field BogoliubovFrameOver.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field BogoliubovFrameOver.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [soft] `law-field-locker` in `structure-field BogoliubovFrameOver.compatible_with_drazin_split` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [soft] `law-field-locker` in `structure-field BogoliubovFrameOver.compatible_with_phase_axis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field BogoliubovFrameOver.compatible_with_krein_form` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [advisory] `existential-packaging` in `def EquivalentBogoliubovFrames` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L162 [advisory] `existential-packaging` in `theorem preserves_drazinProjection_comm` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L171 [advisory] `existential-packaging` in `theorem frame_action` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L178 [soft] `skeletal-proof` in `theorem projected_frame_readout_invariant` — proof appears to close via minimal tactic one-liner

