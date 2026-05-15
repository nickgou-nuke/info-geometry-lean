# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:30.991727+00:00`
Root: `lean/InfoGeometry/Applications/FiniteJonesModel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **3**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Applications/FiniteJonesModel.lean` | `advisory` | 10 | 0 | 3 | 4 | 7 |

## Findings by file

### `lean/InfoGeometry/Applications/FiniteJonesModel.lean`
- module: `InfoGeometry.Applications.FiniteJonesModel`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L160 [soft] `skeletal-proof` in `theorem brewster_kills_p_input` — proof appears to close via minimal tactic one-liner
  - L174 [advisory] `local-hypothesis-injection` in `theorem brewster_kills_p_input` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L180 [soft] `skeletal-proof` in `theorem brewster_scales_s_input` — proof appears to close via minimal tactic one-liner
  - L196 [advisory] `local-hypothesis-injection` in `theorem brewster_scales_s_input` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L226 [soft] `law-field-locker` in `structure-field FiniteJonesEvent.BrewsterWitness.rp_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L243 [advisory] `bridge-shaped-declaration` in `theorem operator_eq_s_core_of_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

