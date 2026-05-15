# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:27.068078+00:00`
Root: `lean/Experimental/SpinorKLBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **6**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/Experimental/SpinorKLBridge.lean` | `advisory` | 13 | 0 | 6 | 1 | 7 |

## Findings by file

### `lean/Experimental/SpinorKLBridge.lean`
- module: `Experimental.SpinorKLBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field SpinorLikelihoodModel.spinorBilinear_nonneg_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field SpinorLikelihoodModel.spinorBilinear_normalizer_pos_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field SpinorLikelihoodModel.normalizedOverlap_def_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field SpinorLikelihoodModel.logLikelihoodRatio_of_spinorBilinear_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field SpinorLikelihoodModel.relativeEntropy_eq_normalizedSpinorOverlap_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field SpinorLikelihoodModel.FenchelLegendre_dual_of_momentPotential_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

