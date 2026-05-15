# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:54.913702+00:00`
Root: `lean/InfoGeometry/Canonical/ConformalAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **14**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ConformalAlgebra.lean` | `advisory` | 36 | 0 | 14 | 8 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/ConformalAlgebra.lean`
- module: `InfoGeometry.Canonical.ConformalAlgebra`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `law-field-locker` in `structure-field ConformalBeliefAlgebra.M` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field ConformalBeliefAlgebra.D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field ConformalBeliefAlgebra.D_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field ConformalBeliefAlgebra.anomaly_breaks_weights` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L79 [soft] `skeletal-proof` in `theorem scale_anomaly_emergence` — proof appears to close via minimal tactic one-liner
  - L100 [soft] `skeletal-proof` in `theorem generatorCartanDecomposition_iff` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `skeletal-proof` in `theorem cartanInvolution_involutive_of_gradingInvolutive` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `skeletal-proof` in `theorem cartanInvolution_eq_self_of_volumePreserving_of_gradingInvolutive` — proof appears to close via minimal tactic one-liner
  - L182 [advisory] `local-hypothesis-injection` in `theorem cartanInvolution_eq_self_of_volumePreserving_of_gradingInvolutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L192 [soft] `skeletal-proof` in `theorem cartanInvolution_eq_neg_self_of_weylDilation_of_gradingInvolutive` — proof appears to close via minimal tactic one-liner
  - L202 [advisory] `local-hypothesis-injection` in `theorem cartanInvolution_eq_neg_self_of_weylDilation_of_gradingInvolutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L204 [advisory] `local-hypothesis-injection` in `theorem cartanInvolution_eq_neg_self_of_weylDilation_of_gradingInvolutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L216 [soft] `skeletal-proof` in `theorem volumePreserving_of_cartanInvolution_eq_self_of_gradingInvolutive` — proof appears to close via minimal tactic one-liner
  - L230 [advisory] `local-hypothesis-injection` in `theorem volumePreserving_of_cartanInvolution_eq_self_of_gradingInvolutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L237 [soft] `skeletal-proof` in `theorem weylDilation_of_cartanInvolution_eq_neg_self_of_gradingInvolutive` — proof appears to close via minimal tactic one-liner
  - L249 [advisory] `local-hypothesis-injection` in `theorem weylDilation_of_cartanInvolution_eq_neg_self_of_gradingInvolutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L257 [advisory] `local-hypothesis-injection` in `theorem weylDilation_of_cartanInvolution_eq_neg_self_of_gradingInvolutive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L288 [soft] `skeletal-proof` in `theorem commutator_volumePreserving_volumePreserving` — proof appears to close via minimal tactic one-liner
  - L312 [soft] `skeletal-proof` in `theorem commutator_volumePreserving_weylDilation` — proof appears to close via minimal tactic one-liner
  - L340 [soft] `skeletal-proof` in `theorem commutator_weylDilation_weylDilation` — proof appears to close via minimal tactic one-liner

