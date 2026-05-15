# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:59.406594+00:00`
Root: `lean/InfoGeometry/Canonical/SpectralInference.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **15**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SpectralInference.lean` | `advisory` | 40 | 0 | 15 | 10 | 25 |

## Findings by file

### `lean/InfoGeometry/Canonical/SpectralInference.lean`
- module: `InfoGeometry.Canonical.SpectralInference`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `simp-law-injection` in `simp-declaration bayesianAction_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L39 [soft] `simp-law-injection` in `simp-declaration bayesianAction_succ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `law-field-locker` in `structure-field SpectralTriple.D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L92 [soft] `law-field-locker` in `structure-field RegularizedSpectralTriple.DD` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field CertifiedRegularizedSpectralTriple.DD` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L122 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L140 [soft] `skeletal-proof` in `theorem spectralProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L145 [advisory] `existential-packaging` in `theorem exists_of_spectralTriple` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L165 [soft] `law-field-locker` in `structure-field ChiralSpectralTriple.DD` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field ChiralSpectralTriple.DP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L176 [soft] `law-field-locker` in `structure-field CertifiedChiralSpectralTriple.DD` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field CertifiedChiralSpectralTriple.DP` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L201 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L239 [soft] `skeletal-proof` in `theorem spectralProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L249 [soft] `skeletal-proof` in `theorem metricProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L260 [soft] `skeletal-proof` in `theorem metricProjector_star` — proof appears to close via minimal tactic one-liner
  - L270 [soft] `skeletal-proof` in `theorem chiralAnomalyOperator_eq_zero_iff_projectors_commute` — proof appears to close via minimal tactic one-liner
  - L278 [soft] `skeletal-proof` in `theorem epsilon_eq_zero_of_projectors_commute` — proof appears to close via minimal tactic one-liner
  - L294 [advisory] `local-hypothesis-injection` in `theorem epsilon_eq_zero_of_projectors_commute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L302 [advisory] `existential-packaging` in `theorem exists_of_spectralTriple` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L331 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

