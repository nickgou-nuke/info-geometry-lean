# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:36.756661+00:00`
Root: `lean/InfoGeometry/Automorphic/ZetaPotentialSign.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **21**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/ZetaPotentialSign.lean` | `advisory` | 47 | 0 | 21 | 5 | 26 |

## Findings by file

### `lean/InfoGeometry/Automorphic/ZetaPotentialSign.lean`
- module: `InfoGeometry.Automorphic.ZetaPotentialSign`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `law-field-locker` in `structure-field JordanBarrierDatum.admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field JordanBarrierDatum.jordanNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field JordanBarrierDatum.jordanNorm_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L57 [soft] `simp-law-injection` in `simp-declaration potential_eq_zero_of_norm_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `skeletal-proof` in `theorem potential_eq_zero_of_norm_eq_one` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `law-field-locker` in `structure-field EulerProductDatum.admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [soft] `law-field-locker` in `structure-field EulerProductDatum.value` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field EulerProductDatum.absValue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field EulerProductDatum.value_nonzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field EulerProductDatum.absValue_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field EulerProductDatum.absValue_eq_norm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L92 [soft] `law-field-locker` in `structure-field EulerProductDatum.localFactor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field EulerProductDatum.eulerProductLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [soft] `simp-law-injection` in `simp-declaration potential_eq_zero_of_absValue_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L122 [soft] `skeletal-proof` in `theorem potential_eq_zero_of_absValue_eq_one` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `law-field-locker` in `structure-field PotentialSignCalibration.potential_nonnegative_iff_absValue_le_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [soft] `law-field-locker` in `structure-field PotentialSignCalibration.potential_zero_iff_absValue_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field ZetaJordanPotentialCorrespondence.toSpectral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `law-field-locker` in `structure-field ZetaJordanPotentialCorrespondence.maps_admissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L171 [soft] `law-field-locker` in `structure-field ZetaJordanPotentialCorrespondence.norm_match` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `skeletal-proof` in `theorem potentials_match` — proof appears to close via minimal tactic one-liner
  - L202 [advisory] `existential-packaging` in `def ArithmeticPotentialOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L212 [advisory] `existential-packaging` in `def ZetaJordanCorrespondenceOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

