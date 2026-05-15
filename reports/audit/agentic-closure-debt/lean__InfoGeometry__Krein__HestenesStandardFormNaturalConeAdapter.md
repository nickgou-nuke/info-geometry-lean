# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:52.944008+00:00`
Root: `lean/InfoGeometry/Krein/HestenesStandardFormNaturalConeAdapter.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **14**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HestenesStandardFormNaturalConeAdapter.lean` | `advisory` | 30 | 0 | 14 | 2 | 16 |

## Findings by file

### `lean/InfoGeometry/Krein/HestenesStandardFormNaturalConeAdapter.lean`
- module: `InfoGeometry.Krein.HestenesStandardFormNaturalConeAdapter`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field HestenesStandardFormNaturalConeAdapter.hestenes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L40 [soft] `section-law-variable` in `variable A` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L69 [soft] `skeletal-proof` in `theorem toCanonical_cone` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `skeletal-proof` in `theorem toCanonical_J` — proof appears to close via minimal tactic one-liner
  - L82 [soft] `skeletal-proof` in `theorem toCanonical_innerReadout` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `skeletal-proof` in `theorem toCanonical_eval` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `theorem toCanonical_coneVector` — proof appears to close via minimal tactic one-liner
  - L103 [soft] `skeletal-proof` in `theorem toCanonical_isNormalPositive` — proof appears to close via minimal tactic one-liner
  - L151 [soft] `law-field-locker` in `structure-field CanonicalRealizedByHestenesKrein.act_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field CanonicalRealizedByHestenesKrein.J_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L158 [soft] `law-field-locker` in `structure-field CanonicalRealizedByHestenesKrein.cone_iff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L162 [soft] `law-field-locker` in `structure-field CanonicalRealizedByHestenesKrein.coneVector_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field CanonicalRealizedByHestenesKrein.eval_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [soft] `law-field-locker` in `structure-field CanonicalRealizedByHestenesKrein.innerReadout_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

