# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:42.911815+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovCartanEigenOperator.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **35**
- Hard: **0**
- Soft: **25**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovCartanEigenOperator.lean` | `advisory` | 60 | 0 | 25 | 10 | 35 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovCartanEigenOperator.lean`
- module: `InfoGeometry.Canonical.BogoliubovCartanEigenOperator`
- status: `advisory`
- debt_score: `60`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L45 [soft] `skeletal-proof` in `theorem cartanAdjoint_eq_transportCommutator` — proof appears to close via minimal tactic one-liner
  - L54 [soft] `simp-law-injection` in `simp-declaration zero_isCartanEigenOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `simp-law-injection` in `simp-declaration cartanAdjoint_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration cartanAdjoint_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration cartanAdjoint_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `skeletal-proof` in `theorem cartanEigenOperator_commutator` — proof appears to close via minimal tactic one-liner
  - L197 [soft] `skeletal-proof` in `theorem cartanEigenOperator_conjugate` — proof appears to close via minimal tactic one-liner
  - L301 [soft] `skeletal-proof` in `theorem maps_regular_sector` — proof appears to close via minimal tactic one-liner
  - L314 [soft] `skeletal-proof` in `theorem maps_null_sector` — proof appears to close via minimal tactic one-liner
  - L327 [soft] `skeletal-proof` in `theorem inverse_maps_regular_sector` — proof appears to close via minimal tactic one-liner
  - L334 [advisory] `local-hypothesis-injection` in `theorem inverse_maps_regular_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L338 [advisory] `local-hypothesis-injection` in `theorem inverse_maps_regular_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L347 [soft] `skeletal-proof` in `theorem inverse_maps_null_sector` — proof appears to close via minimal tactic one-liner
  - L354 [advisory] `local-hypothesis-injection` in `theorem inverse_maps_null_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L358 [advisory] `local-hypothesis-injection` in `theorem inverse_maps_null_sector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L377 [soft] `skeletal-proof` in `theorem maps_chiral_sector` — proof appears to close via minimal tactic one-liner
  - L414 [soft] `law-field-locker` in `structure-field CartanExponentialAdjointCalibration.expCartan` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L416 [soft] `law-field-locker` in `structure-field CartanExponentialAdjointCalibration.expCartan_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L419 [soft] `law-field-locker` in `structure-field CartanExponentialAdjointCalibration.eigen_adjointFlow_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L482 [advisory] `local-hypothesis-injection` in `theorem adjointExponentialFlow_add_on_eigenoperator` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L502 [soft] `law-field-locker` in `structure-field CartanFrameEquiv.left_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L505 [soft] `law-field-locker` in `structure-field CartanFrameEquiv.right_inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L508 [soft] `law-field-locker` in `structure-field CartanFrameEquiv.conjugatesCartan` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L516 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L516 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L530 [soft] `law-field-locker` in `structure-field BogoliubovCartanFrameEquiv.cartan` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L533 [soft] `law-field-locker` in `structure-field BogoliubovCartanFrameEquiv.preservesPreg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L537 [soft] `law-field-locker` in `structure-field BogoliubovCartanFrameEquiv.preservesPzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L541 [soft] `law-field-locker` in `structure-field BogoliubovCartanFrameEquiv.preservesGammaS` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L545 [soft] `law-field-locker` in `structure-field BogoliubovCartanFrameEquiv.preservesKrein` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L563 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L563 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

