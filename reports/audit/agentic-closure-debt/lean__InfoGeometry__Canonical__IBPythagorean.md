# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:18.831510+00:00`
Root: `lean/InfoGeometry/Canonical/IBPythagorean.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **0**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBPythagorean.lean` | `advisory` | 12 | 0 | 0 | 12 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBPythagorean.lean`
- module: `InfoGeometry.Canonical.IBPythagorean`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L53 [advisory] `existential-packaging` in `lemma IBMarginalize_eq_encoderKernel_comp` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L66 [advisory] `existential-packaging` in `lemma llr_chain_rule` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L93 [advisory] `existential-packaging` in `lemma klDiv_eq_klDiv_add_integral_llr` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L247 [advisory] `existential-packaging` in `abbrev IBNextMarginalDescentWitness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L270 [advisory] `existential-packaging` in `theorem ibMarginalPythagorean_identity_of_marginalization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L348 [advisory] `local-hypothesis-injection` in `theorem ibMarginalPythagorean_identity_of_marginalization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L450 [advisory] `existential-packaging` in `theorem ibNextMarginalPythagoreanWitness_of_marginalization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L491 [advisory] `existential-packaging` in `theorem IBMarginalDescentWitness.of_pythagorean` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L508 [advisory] `bridge-shaped-declaration` in `theorem IB_marginal_descent_of_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L508 [advisory] `existential-packaging` in `theorem IB_marginal_descent_of_witness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L539 [advisory] `bridge-shaped-declaration` in `theorem IB_next_marginal_descent_of_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

