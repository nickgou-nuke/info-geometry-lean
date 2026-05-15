# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:11.945016+00:00`
Root: `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **0**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GrandSynthesis.lean` | `advisory` | 5 | 0 | 0 | 5 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- module: `InfoGeometry.Canonical.GrandSynthesis`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L44 [advisory] `existential-packaging` in `theorem canopy_geometric_component_constant` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L69 [advisory] `existential-packaging` in `theorem grandSynthesis_trunk_to_canopy_closure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L93 [advisory] `existential-packaging` in `theorem grandSynthesis_root_factorization` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

