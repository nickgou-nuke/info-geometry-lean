# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:49.938192+00:00`
Root: `lean/InfoGeometry/Canonical/CertifiedModularReduction.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **22**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CertifiedModularReduction.lean` | `advisory` | 51 | 0 | 22 | 7 | 29 |

## Findings by file

### `lean/InfoGeometry/Canonical/CertifiedModularReduction.lean`
- module: `InfoGeometry.Canonical.CertifiedModularReduction`
- status: `advisory`
- debt_score: `51`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L64 [soft] `law-field-locker` in `structure-field CertifiedModularReduction.logAdmissible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field CertifiedModularReduction.logOn` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field CertifiedModularReduction.hRegularSpectrumPositive_to_logDomain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field CertifiedModularReduction.hPmetricKrein` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field CertifiedModularReduction.hKambient_supported_on_Preg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [soft] `law-field-locker` in `structure-field CertifiedModularReduction.hKambient_kills_Pzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field CertifiedModularReduction.hKphys_supported_on_metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field CertifiedModularReduction.hAnomaly_zero_iff_alignment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L114 [soft] `section-law-variable` in `variable c` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L192 [soft] `skeletal-proof` in `theorem Kambient_supported_on_Preg` — proof appears to close via minimal tactic one-liner
  - L198 [soft] `skeletal-proof` in `theorem Kambient_kills_Pzero` — proof appears to close via minimal tactic one-liner
  - L210 [soft] `skeletal-proof` in `theorem Kphys_supported_on_metric` — proof appears to close via minimal tactic one-liner
  - L218 [soft] `skeletal-proof` in `theorem anomaly_zero_iff_alignment` — proof appears to close via minimal tactic one-liner
  - L237 [soft] `skeletal-proof` in `theorem Pzero_commutes_Pmetric_of_alignment` — proof appears to close via minimal tactic one-liner
  - L240 [advisory] `local-hypothesis-injection` in `theorem Pzero_commutes_Pmetric_of_alignment` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L259 [soft] `skeletal-proof` in `theorem Kphys_kills_Pzero_of_alignment` — proof appears to close via minimal tactic one-liner
  - L266 [advisory] `local-hypothesis-injection` in `theorem Kphys_kills_Pzero_of_alignment` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L333 [soft] `simp-law-injection` in `simp-declaration modularLieDerivation_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L335 [soft] `skeletal-proof` in `theorem modularLieDerivation_apply` — proof appears to close via minimal tactic one-liner
  - L343 [soft] `simp-law-injection` in `simp-declaration modularLieHessian_eq_nested_commutator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L345 [soft] `skeletal-proof` in `theorem modularLieHessian_eq_nested_commutator` — proof appears to close via minimal tactic one-liner
  - L361 [soft] `skeletal-proof` in `theorem deriv_modularTransportedObservable_at_zero` — proof appears to close via minimal tactic one-liner
  - L373 [soft] `skeletal-proof` in `theorem deriv2_modularTransportedObservable_at_zero` — proof appears to close via minimal tactic one-liner
  - L379 [advisory] `local-hypothesis-injection` in `theorem deriv2_modularTransportedObservable_at_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L386 [advisory] `local-hypothesis-injection` in `theorem deriv2_modularTransportedObservable_at_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L396 [soft] `skeletal-proof` in `theorem modularLieDerivation_gaugeShift` — proof appears to close via minimal tactic one-liner

