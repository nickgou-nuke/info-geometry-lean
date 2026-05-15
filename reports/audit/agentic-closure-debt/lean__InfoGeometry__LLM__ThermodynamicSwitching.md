# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:57.994983+00:00`
Root: `lean/InfoGeometry/LLM/ThermodynamicSwitching.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **6**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/ThermodynamicSwitching.lean` | `advisory` | 17 | 0 | 6 | 5 | 11 |

## Findings by file

### `lean/InfoGeometry/LLM/ThermodynamicSwitching.lean`
- module: `InfoGeometry.LLM.ThermodynamicSwitching`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field SwitchMask.active` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [advisory] `existential-packaging` in `lemma maskedNormalizedWeight_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L77 [advisory] `existential-packaging` in `theorem allTop_weights_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L96 [advisory] `existential-packaging` in `theorem exists_modewiseClifford_rep_of_bistochastic_switch` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L96 [soft] `skeletal-proof` in `theorem exists_modewiseClifford_rep_of_bistochastic_switch` — proof appears to close via minimal tactic one-liner
  - L130 [advisory] `bridge-shaped-declaration` in `theorem arnoldNetwork_preserves_submodule_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L130 [soft] `skeletal-proof` in `theorem arnoldNetwork_preserves_submodule_bridge` — proof appears to close via minimal tactic one-liner
  - L169 [soft] `skeletal-proof` in `theorem arnoldTaggedPresentation_lane` — proof appears to close via minimal tactic one-liner
  - L181 [soft] `skeletal-proof` in `theorem arnoldQuantumPresentation_generator_eq_arnold` — proof appears to close via minimal tactic one-liner
  - L196 [soft] `skeletal-proof` in `theorem arnoldQuantumPresentation_generator_mem_submodule` — proof appears to close via minimal tactic one-liner

