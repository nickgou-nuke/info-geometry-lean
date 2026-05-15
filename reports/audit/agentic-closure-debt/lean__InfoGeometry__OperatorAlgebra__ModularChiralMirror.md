# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:18.191530+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ModularChiralMirror.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **37**
- Hard: **0**
- Soft: **30**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ModularChiralMirror.lean` | `advisory` | 67 | 0 | 30 | 7 | 37 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ModularChiralMirror.lean`
- module: `InfoGeometry.OperatorAlgebra.ModularChiralMirror`
- status: `advisory`
- debt_score: `67`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `law-field-locker` in `structure-field ModularChiralMirrorSign.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field ModularChiralMirrorSign.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field ModularChiralMirrorSign.J_flips_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field ModularChiralMirrorDatum.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field ModularChiralMirrorDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field ModularChiralMirrorDatum.J_flips_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L141 [soft] `skeletal-proof` in `theorem J_mul_one_add_chi` — proof appears to close via minimal tactic one-liner
  - L164 [soft] `skeletal-proof` in `theorem J_mul_one_sub_chi` — proof appears to close via minimal tactic one-liner
  - L320 [soft] `law-field-locker` in `structure-field LinearDatum.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L322 [soft] `law-field-locker` in `structure-field LinearDatum.chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L325 [soft] `law-field-locker` in `structure-field LinearDatum.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L329 [soft] `law-field-locker` in `structure-field LinearDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L333 [soft] `law-field-locker` in `structure-field LinearDatum.J_flips_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L342 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L486 [soft] `law-field-locker` in `structure-field ModularChiralMirrorDatum.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L490 [soft] `law-field-locker` in `structure-field ModularChiralMirrorDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L494 [soft] `law-field-locker` in `structure-field ModularChiralMirrorDatum.J_flips_chi` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L503 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L697 [soft] `skeletal-proof` in `theorem chiralCharge_J` — proof appears to close via minimal tactic one-liner
  - L739 [soft] `law-field-locker` in `structure-field ModularChiralChargeDatum.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L743 [soft] `law-field-locker` in `structure-field ModularChiralChargeDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L747 [soft] `law-field-locker` in `structure-field ModularChiralChargeDatum.J_chi_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L751 [soft] `law-field-locker` in `structure-field ModularChiralChargeDatum.J_isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L761 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L788 [soft] `skeletal-proof` in `theorem chiralCharge_J` — proof appears to close via minimal tactic one-liner
  - L827 [soft] `law-field-locker` in `structure-field AlgebraCommutantChiralMirror.InAlgebra` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L830 [soft] `law-field-locker` in `structure-field AlgebraCommutantChiralMirror.InCommutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L833 [soft] `law-field-locker` in `structure-field AlgebraCommutantChiralMirror.algebra_mirrors_to_commutant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L839 [soft] `law-field-locker` in `structure-field AlgebraCommutantChiralMirror.mirror_flips_chiral_charge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L939 [soft] `law-field-locker` in `structure-field SignedModularChiralMirrorDatum.J_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L943 [soft] `law-field-locker` in `structure-field SignedModularChiralMirrorDatum.chi_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L969 [soft] `law-field-locker` in `structure-field ModularChiralSignDatum.preserves_relation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L974 [soft] `law-field-locker` in `structure-field ModularChiralSignDatum.flips_relation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L979 [advisory] `existential-packaging` in `def ModularChiralMirrorOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L989 [advisory] `existential-packaging` in `def AlgebraicModularChiralMirrorOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

