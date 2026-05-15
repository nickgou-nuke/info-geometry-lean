# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:49.746893+00:00`
Root: `lean/InfoGeometry/TransformationGroups.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **4**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/TransformationGroups.lean` | `advisory` | 21 | 0 | 4 | 13 | 17 |

## Findings by file

### `lean/InfoGeometry/TransformationGroups.lean`
- module: `InfoGeometry.TransformationGroups`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [advisory] `existential-packaging` in `def is_transitive` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L38 [advisory] `existential-packaging` in `lemma uniform_of_all_eq` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L38 [soft] `classical-witness-smuggling` in `lemma uniform_of_all_eq` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L38 [soft] `skeletal-proof` in `lemma uniform_of_all_eq` — proof appears to close via minimal tactic one-liner
  - L47 [advisory] `local-hypothesis-injection` in `lemma uniform_of_all_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L50 [advisory] `local-hypothesis-injection` in `lemma uniform_of_all_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L52 [advisory] `local-hypothesis-injection` in `lemma uniform_of_all_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L54 [advisory] `local-hypothesis-injection` in `lemma uniform_of_all_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L56 [advisory] `local-hypothesis-injection` in `lemma uniform_of_all_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L58 [advisory] `local-hypothesis-injection` in `lemma uniform_of_all_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L59 [advisory] `local-hypothesis-injection` in `lemma uniform_of_all_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L62 [advisory] `local-hypothesis-injection` in `lemma uniform_of_all_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L75 [advisory] `existential-packaging` in `theorem uniform_of_transformation_group` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L104 [soft] `skeletal-proof` in `lemma scale_invariant_inv` — proof appears to close via minimal tactic one-liner
  - L110 [advisory] `local-hypothesis-injection` in `lemma scale_invariant_inv` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L115 [soft] `skeletal-proof` in `lemma log_coord_flat` — proof appears to close via minimal tactic one-liner

